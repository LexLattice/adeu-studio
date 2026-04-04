from __future__ import annotations

import random
from collections import Counter
from statistics import mean

from .actions import (
    ACTION_LIBRARY,
    ACTION_ORDER_INDEX,
    FROZEN_ACTION_TYPE_ORDER,
    get_action_contracts,
)
from .metrics import clamp, compute_metrics
from .models import (
    Action,
    ActionType,
    Agent,
    Archetype,
    AuditResult,
    Claim,
    DeonticStatus,
    DState,
    EState,
    EventRecord,
    EventRecordKind,
    EvidenceRecord,
    Institution,
    LaneDelta,
    Norm,
    NormModality,
    Observation,
    OState,
    PublicReport,
    ResourcePool,
    SanctionEvent,
    ScenarioConfig,
    UState,
    WorldState,
)
from .scenarios import (
    CANONICAL_REPLAY_HORIZON,
    CANONICAL_REPLAY_SEED,
    DEFAULT_SCENARIO_NAME,
    get_scenario,
)


class ODEUSimulation:
    def __init__(self) -> None:
        self.rng = random.Random(CANONICAL_REPLAY_SEED)
        self._id_counter = 0
        self.state: WorldState | None = None
        self.reset(DEFAULT_SCENARIO_NAME, seed=CANONICAL_REPLAY_SEED)

    def reset(
        self, scenario_name: str = DEFAULT_SCENARIO_NAME, seed: int = CANONICAL_REPLAY_SEED
    ) -> WorldState:
        self.rng = random.Random(seed)
        self._id_counter = 0
        config = get_scenario(scenario_name)
        self.state = self._build_world(config=config, seed=seed)
        metric = compute_metrics(self.state)
        self.state.metrics_history = [metric]
        self._record_event(
            EventRecordKind.REGIME_CLASSIFIED,
            turn=0,
            summary=f"Initial regime classified as {metric.regime_label.value}",
            related_ids=(),
        )
        return self.state

    def step(self, steps: int = 1) -> WorldState:
        for _ in range(max(1, steps)):
            self._step_once()
        return self.get_state()

    def run(self, steps: int = CANONICAL_REPLAY_HORIZON) -> WorldState:
        return self.step(steps=steps)

    def get_state(self) -> WorldState:
        if self.state is None:
            raise RuntimeError("simulation not initialized")
        return self.state

    def _build_world(self, config: ScenarioConfig, seed: int) -> WorldState:
        resource_pool = ResourcePool(
            stock=100.0 * (1.0 - config.scarcity),
            capacity=100.0,
            regeneration_rate=config.regeneration_rate,
            extraction_damage=1.0 + config.scarcity * 0.3,
        )
        institution = Institution(
            id="inst_civic",
            name="Commons Stewardship Council",
            legitimacy=config.initial_legitimacy,
            operativity=config.initial_operativity,
            enforcement_capacity=config.enforcement_capacity,
            enforcement_remaining=config.enforcement_capacity,
            sanction_consistency=config.sanction_consistency,
            appeal_availability=config.appeal_availability,
            archive_capacity=config.archive_capacity,
            public_epistemics_level=config.public_epistemics_level,
            budget=4.0,
            capture_pressure=0.0,
        )
        world = WorldState(
            seed=seed,
            scenario=config.name,
            config=config,
            resource_pool=resource_pool,
            institution=institution,
            norms=self._build_norms(),
            agents=self._build_agents(config, resource_pool, institution),
        )
        self._record_event(
            EventRecordKind.SIMULATION_INITIALIZED,
            turn=0,
            summary=f"Initialized scenario {config.name} with seed {seed}",
            related_ids=(institution.id, resource_pool.id),
            world=world,
        )
        return world

    def _build_norms(self) -> list[Norm]:
        norms = [
            Norm(
                id="commons_stewardship",
                modality=NormModality.PROHIBITION,
                subject_scope="all_agents",
                trigger_condition="always_active",
                target_action=ActionType.DEFECT,
                sanction_rule="resource_fine",
                appeal_available=True,
                legitimacy_contribution=0.25,
                enforcement_cost=0.8,
                observability_dependency=0.45,
            ),
            Norm(
                id="truthful_public_reporting",
                modality=NormModality.PROHIBITION,
                subject_scope="all_agents",
                trigger_condition="when_reporting",
                target_action=ActionType.MISREPORT,
                sanction_rule="reputation_and_resource_fine",
                appeal_available=True,
                legitimacy_contribution=0.2,
                enforcement_cost=0.5,
                observability_dependency=0.55,
            ),
            Norm(
                id="steward_contribution_duty",
                modality=NormModality.OBLIGATION,
                subject_scope="all_agents",
                trigger_condition="commons_believed_low",
                target_action=ActionType.CONTRIBUTE,
                sanction_rule="social_censure",
                appeal_available=False,
                legitimacy_contribution=0.15,
                enforcement_cost=0.2,
                observability_dependency=0.2,
            ),
            Norm(
                id="official_due_process",
                modality=NormModality.ROLE_DUTY,
                subject_scope="officials",
                trigger_condition="pending_cases_with_evidence",
                target_action=ActionType.SANCTION,
                sanction_rule="institutional_backlog_penalty",
                appeal_available=True,
                legitimacy_contribution=0.3,
                enforcement_cost=0.7,
                observability_dependency=0.7,
            ),
        ]
        norms.sort(key=lambda norm: norm.id)
        return norms

    def _build_agents(
        self, config: ScenarioConfig, resource_pool: ResourcePool, institution: Institution
    ) -> list[Agent]:
        counts = self._resolve_archetype_counts(config)
        archetypes: list[Archetype] = []
        for archetype in (
            Archetype.COOPERATOR,
            Archetype.OPPORTUNIST,
            Archetype.AUDITOR,
            Archetype.OFFICIAL,
            Archetype.AI_DEPENDENT,
        ):
            archetypes.extend([archetype] * counts[archetype])
        self.rng.shuffle(archetypes)
        agent_ids = [f"agent_{index:02d}" for index in range(len(archetypes))]
        peer_network = self._build_peer_network(agent_ids)
        agents: list[Agent] = []
        for index, archetype in enumerate(archetypes):
            belief_noise = self.rng.uniform(-10.0, 10.0)
            belief = clamp(resource_pool.stock + belief_noise, 0.0, resource_pool.capacity)
            uncertainty = clamp(0.35 + config.misinformation * 0.4 + self.rng.uniform(-0.08, 0.08))
            base_income = self.rng.uniform(0.8, 1.25)
            if archetype == Archetype.COOPERATOR:
                params = self._archetype_params(
                    greed=(0.18, 0.38),
                    fairness=(0.68, 0.9),
                    horizon=(0.6, 0.88),
                    risk=(0.2, 0.5),
                    sanction=(0.55, 0.8),
                    norm=(0.7, 0.92),
                    duty=(0.15, 0.35),
                    evidence=(0.45, 0.65),
                    verification=(
                        config.verification_capacity - 0.05,
                        config.verification_capacity + 0.08,
                    ),
                    vigilance=(0.45, 0.68),
                    resources=(4.5, 7.0),
                )
            elif archetype == Archetype.OPPORTUNIST:
                params = self._archetype_params(
                    greed=(0.65, 0.95),
                    fairness=(0.08, 0.3),
                    horizon=(0.15, 0.45),
                    risk=(0.55, 0.9),
                    sanction=(0.15, 0.45),
                    norm=(0.1, 0.35),
                    duty=(0.05, 0.2),
                    evidence=(0.25, 0.45),
                    verification=(
                        config.verification_capacity - 0.15,
                        config.verification_capacity + 0.03,
                    ),
                    vigilance=(0.1, 0.28),
                    resources=(4.5, 7.5),
                )
            elif archetype == Archetype.AUDITOR:
                params = self._archetype_params(
                    greed=(0.18, 0.35),
                    fairness=(0.58, 0.82),
                    horizon=(0.45, 0.8),
                    risk=(0.25, 0.55),
                    sanction=(0.45, 0.72),
                    norm=(0.62, 0.88),
                    duty=(0.55, 0.85),
                    evidence=(0.62, 0.85),
                    verification=(
                        config.verification_capacity + 0.08,
                        config.verification_capacity + 0.18,
                    ),
                    vigilance=(0.75, 0.95),
                    resources=(4.0, 6.5),
                )
            elif archetype == Archetype.OFFICIAL:
                params = self._archetype_params(
                    greed=(0.25, 0.45),
                    fairness=(0.5, 0.78),
                    horizon=(0.48, 0.82),
                    risk=(0.18, 0.45),
                    sanction=(0.42, 0.68),
                    norm=(0.6, 0.88),
                    duty=(0.82, 0.98),
                    evidence=(0.5, 0.72),
                    verification=(
                        config.verification_capacity + 0.02,
                        config.verification_capacity + 0.12,
                    ),
                    vigilance=(0.55, 0.78),
                    resources=(4.5, 6.8),
                )
            else:
                params = self._archetype_params(
                    greed=(0.32, 0.55),
                    fairness=(0.35, 0.6),
                    horizon=(0.4, 0.72),
                    risk=(0.35, 0.58),
                    sanction=(0.4, 0.7),
                    norm=(0.38, 0.65),
                    duty=(0.15, 0.3),
                    evidence=(0.28, 0.48),
                    verification=(
                        config.verification_capacity - 0.08,
                        config.verification_capacity + 0.05,
                    ),
                    vigilance=(0.25, 0.45),
                    resources=(4.2, 6.8),
                )
            trust_ai = 0.2 if config.ai_mode.value == "none" else self.rng.uniform(0.4, 0.9)
            if archetype == Archetype.AI_DEPENDENT:
                trust_ai = max(trust_ai, self.rng.uniform(0.75, 0.95))
            peer_trust = {
                peer_id: self.rng.uniform(0.35, 0.75) for peer_id in peer_network[agent_ids[index]]
            }
            agents.append(
                Agent(
                    id=agent_ids[index],
                    archetype=archetype,
                    o_state=OState(
                        resources=params["resources"],
                        base_income=base_income,
                        evidence_access=params["evidence"],
                    ),
                    e_state=EState(
                        belief_commons=belief,
                        uncertainty=uncertainty,
                        evidence_access=params["evidence"],
                        verification_capacity=clamp(params["verification"]),
                        epistemic_vigilance=params["vigilance"],
                        trust_institution=clamp(
                            institution.legitimacy + self.rng.uniform(-0.18, 0.12)
                        ),
                        trust_ai=clamp(trust_ai),
                        peer_trust=peer_trust,
                    ),
                    d_state=DState(
                        norm_commitment=params["norm"],
                        legitimacy_belief=clamp(
                            institution.legitimacy + self.rng.uniform(-0.12, 0.08)
                        ),
                        role_duty_strength=params["duty"],
                        appeal_propensity=self.rng.uniform(0.35, 0.8),
                        compliance_bias=clamp((params["norm"] + params["fairness"]) / 2),
                    ),
                    u_state=UState(
                        greed=params["greed"],
                        long_term_horizon=params["horizon"],
                        fairness=params["fairness"],
                        risk_tolerance=params["risk"],
                        sanction_aversion=params["sanction"],
                    ),
                )
            )
        agents.sort(key=lambda agent: agent.id)
        return agents

    def _archetype_params(self, **ranges: tuple[float, float]) -> dict[str, float]:
        params: dict[str, float] = {}
        for name, (low, high) in ranges.items():
            params[name] = clamp(self.rng.uniform(low, high))
        return params

    def _resolve_archetype_counts(self, config: ScenarioConfig) -> dict[Archetype, int]:
        weights = {
            Archetype.COOPERATOR: config.cooperator_share,
            Archetype.OPPORTUNIST: config.opportunist_share,
            Archetype.AUDITOR: config.auditor_share,
            Archetype.OFFICIAL: config.official_share,
            Archetype.AI_DEPENDENT: config.ai_dependent_share,
        }
        counts = {archetype: int(config.num_agents * share) for archetype, share in weights.items()}
        while sum(counts.values()) < config.num_agents:
            target = max(weights, key=weights.get)
            counts[target] += 1
            weights[target] = max(0.0, weights[target] - 0.01)
        while sum(counts.values()) > config.num_agents:
            target = max(counts, key=counts.get)
            counts[target] -= 1
        return counts

    def _build_peer_network(self, agent_ids: list[str]) -> dict[str, list[str]]:
        size = len(agent_ids)
        adjacency = {agent_id: set() for agent_id in agent_ids}
        for index, agent_id in enumerate(agent_ids):
            adjacency[agent_id].add(agent_ids[(index - 1) % size])
            adjacency[agent_id].add(agent_ids[(index + 1) % size])
        extra_edges = max(1, size // 4)
        for _ in range(extra_edges):
            left, right = self.rng.sample(agent_ids, 2)
            adjacency[left].add(right)
            adjacency[right].add(left)
        return {agent_id: sorted(neighbors) for agent_id, neighbors in adjacency.items()}

    def _step_once(self) -> None:
        world = self.get_state()
        if world.turn >= world.config.max_turns:
            raise RuntimeError("max_turns reached")
        world.turn += 1
        world.planned_actions = []
        self._record_event(
            EventRecordKind.TURN_STARTED,
            turn=world.turn,
            summary=f"Turn {world.turn} started",
            related_ids=(),
        )
        self._update_ontology(world)
        self._observe_world(world)
        planned_actions = self.plan_actions(world)
        world.planned_actions = planned_actions
        for action in planned_actions:
            self._record_event(
                EventRecordKind.PLANNED_ACTION,
                turn=world.turn,
                summary=f"{action.actor_id} planned {action.action_type.value}",
                related_ids=(action.actor_id, *action.targets),
            )
            self._apply_action(world, action)
        self._emit_public_report(world)
        self._update_epistemics(world)
        metric = compute_metrics(world)
        world.metrics_history.append(metric)
        self._record_event(
            EventRecordKind.REGIME_CLASSIFIED,
            turn=world.turn,
            summary=f"Turn {world.turn} regime classified as {metric.regime_label.value}",
            related_ids=(),
        )
        self._record_event(
            EventRecordKind.TURN_COMPLETED,
            turn=world.turn,
            summary=f"Turn {world.turn} completed with {len(planned_actions)} actions",
            related_ids=tuple(action.id for action in planned_actions),
        )

    def _update_ontology(self, world: WorldState) -> None:
        commons = world.resource_pool
        commons.stock = clamp(
            commons.stock + commons.regeneration_rate * (commons.capacity - commons.stock),
            0.0,
            commons.capacity,
        )
        world.institution.enforcement_remaining = clamp(
            world.institution.enforcement_capacity * (0.45 + 0.55 * world.institution.operativity)
        )
        for agent in self._iter_agents(world):
            agent.o_state.resources += agent.o_state.base_income
            if agent.o_state.sanctioned_last_turn:
                agent.o_state.resources = max(0.0, agent.o_state.resources - 0.2)
                agent.o_state.sanctioned_last_turn = False
        self._record_event(
            EventRecordKind.DIAGNOSTIC_NOTE,
            turn=world.turn,
            summary=f"Commons regenerated to {commons.stock:.2f} and enforcement reset",
            related_ids=(commons.id, world.institution.id),
        )

    def _observe_world(self, world: WorldState) -> None:
        for agent in self._iter_agents(world):
            signal_noise = (
                0.12 + world.config.misinformation * 0.25
            ) * world.resource_pool.capacity
            signal_noise *= 1.1 - 0.4 * agent.e_state.evidence_access
            observed = clamp(
                world.resource_pool.stock + self.rng.gauss(0.0, signal_noise),
                0.0,
                world.resource_pool.capacity,
            )
            confidence = clamp(1.0 - signal_noise / world.resource_pool.capacity)
            world.observations.append(
                Observation(
                    id=self._next_id("obs"),
                    turn=world.turn,
                    observer_id=agent.id,
                    kind="local_stock_trace",
                    proposition="commons_stock",
                    value=observed,
                    confidence=confidence,
                    raw_text=f"Local commons signal {observed:.1f}",
                )
            )

    def plan_actions(self, world: WorldState) -> list[Action]:
        planned: list[Action] = []
        for agent in self._iter_agents(world):
            planned.append(self._select_action_for_agent(world, agent))
        planned.sort(key=lambda action: action.actor_id)
        return planned

    def _select_action_for_agent(self, world: WorldState, agent: Agent) -> Action:
        candidates: list[tuple[float, int, tuple[str, ...], Action]] = []
        for action_type in FROZEN_ACTION_TYPE_ORDER:
            template = ACTION_LIBRARY[action_type]
            if not self._is_eligible(agent, template):
                continue
            if agent.o_state.resources < template.material_cost:
                continue
            targets = self._select_targets_for_action(world, agent, action_type)
            score = self._score_action(world, agent, action_type, targets)
            if score is None:
                continue
            status = self._evaluate_deontics(world, agent, action_type)
            action = Action(
                id=self._next_id("act"),
                turn=world.turn,
                actor_id=agent.id,
                action_type=action_type,
                targets=targets,
                material_cost=template.material_cost,
                observability=template.observability,
                evidence_emission=template.evidence_emission,
                deontic_status=status,
                lane_impact=template.lane_impact.model_copy(deep=True),
                rationale=f"score={score:.4f}",
            )
            candidates.append((score, ACTION_ORDER_INDEX[action_type], targets, action))
        if not candidates:
            template = ACTION_LIBRARY[ActionType.DO_NOTHING]
            return Action(
                id=self._next_id("act"),
                turn=world.turn,
                actor_id=agent.id,
                action_type=ActionType.DO_NOTHING,
                material_cost=template.material_cost,
                observability=template.observability,
                evidence_emission=template.evidence_emission,
                deontic_status=template.base_deontic_status,
                lane_impact=template.lane_impact.model_copy(deep=True),
                rationale="fallback",
            )
        candidates.sort(key=lambda item: (-item[0], item[1], item[2]))
        return candidates[0][3]

    def _is_eligible(self, agent: Agent, template) -> bool:
        if "all" in template.actor_eligibility:
            return True
        return agent.archetype.value in template.actor_eligibility

    def _select_targets_for_action(
        self, world: WorldState, agent: Agent, action_type: ActionType
    ) -> tuple[str, ...]:
        if action_type == ActionType.AUDIT:
            return (world.institution.id,)
        if action_type == ActionType.APPEAL:
            return (world.institution.id,) if agent.o_state.pending_appeal else ()
        if action_type == ActionType.SANCTION:
            target = self._select_sanction_target(world)
            return (target,) if target is not None else ()
        if action_type == ActionType.INVEST_E:
            return ("public_archive",)
        if action_type == ActionType.INVEST_D:
            return (world.institution.id,)
        if action_type in {ActionType.SHARE_CLAIM, ActionType.MISREPORT}:
            return ("public_archive",)
        return ()

    def _evaluate_deontics(
        self, world: WorldState, agent: Agent, action_type: ActionType
    ) -> DeonticStatus:
        commons_ratio = world.resource_pool.stock / world.resource_pool.capacity
        symbolic_gap = 1.0 - world.institution.operativity
        if action_type in {ActionType.DEFECT, ActionType.MISREPORT}:
            return DeonticStatus.FORBIDDEN
        if action_type == ActionType.CONTRIBUTE:
            return DeonticStatus.REQUIRED if commons_ratio < 0.55 else DeonticStatus.PERMITTED
        if action_type == ActionType.VERIFY:
            return (
                DeonticStatus.REQUIRED
                if agent.e_state.uncertainty > 0.62 and agent.e_state.epistemic_vigilance > 0.55
                else DeonticStatus.PERMITTED
            )
        if action_type == ActionType.AUDIT:
            return (
                DeonticStatus.REQUIRED
                if agent.archetype in {Archetype.AUDITOR, Archetype.OFFICIAL}
                and (
                    world.institution.legitimacy < 0.55
                    or world.institution.sanction_consistency < 0.45
                    or symbolic_gap > 0.35
                )
                else DeonticStatus.PERMITTED
            )
        if action_type == ActionType.SANCTION:
            return (
                DeonticStatus.REQUIRED
                if self._strongest_case_confidence(world) >= 0.42
                else DeonticStatus.CONTESTABLE
            )
        if action_type == ActionType.INVEST_D and world.institution.operativity < 0.38:
            return (
                DeonticStatus.REQUIRED
                if agent.archetype == Archetype.OFFICIAL
                else DeonticStatus.PERMITTED
            )
        return DeonticStatus.PERMITTED

    def _score_action(
        self,
        world: WorldState,
        agent: Agent,
        action_type: ActionType,
        targets: tuple[str, ...],
    ) -> float | None:
        commons_ratio = world.resource_pool.stock / world.resource_pool.capacity
        legitimacy = world.institution.legitimacy
        symbolic_gap = 1.0 - world.institution.operativity
        evidence_gap = 1.0 - world.institution.public_epistemics_level
        enforcement = world.institution.enforcement_remaining
        status = self._evaluate_deontics(world, agent, action_type)
        normative_force = (
            0.55 * agent.d_state.norm_commitment
            + 0.35 * agent.d_state.legitimacy_belief
            + 0.25 * agent.u_state.sanction_aversion * enforcement
            + 0.15 * agent.d_state.role_duty_strength
        )
        if status == DeonticStatus.FORBIDDEN and normative_force >= (
            agent.u_state.greed + agent.u_state.risk_tolerance
        ):
            return None
        score = 0.05
        if action_type == ActionType.CONTRIBUTE:
            score = (
                1.2 * agent.u_state.fairness
                + 0.8 * agent.d_state.norm_commitment
                + 0.5 * legitimacy
                + (1.0 - commons_ratio)
                - 0.8 * agent.u_state.greed
            )
        elif action_type == ActionType.DEFECT:
            score = (
                1.3 * agent.u_state.greed
                + (0.6 - commons_ratio)
                + (0.5 - enforcement * agent.u_state.sanction_aversion)
                - 0.8 * agent.d_state.norm_commitment
                - 0.5 * agent.u_state.fairness
            )
        elif action_type == ActionType.SHARE_CLAIM:
            score = (
                0.35
                + 0.4 * (1.0 - agent.e_state.uncertainty)
                + 0.2 * world.institution.public_epistemics_level
            )
        elif action_type == ActionType.MISREPORT:
            score = (
                0.7 * agent.u_state.greed
                + 0.4 * world.config.misinformation
                - 0.7 * agent.e_state.epistemic_vigilance
                - 0.6 * agent.d_state.norm_commitment
            )
        elif action_type == ActionType.VERIFY:
            score = (
                0.9 * agent.e_state.uncertainty
                + 0.8 * agent.e_state.verification_capacity
                + 0.4 * agent.e_state.epistemic_vigilance
                - 0.3 * agent.u_state.greed
            )
        elif action_type == ActionType.AUDIT:
            score = (
                0.9 * agent.d_state.role_duty_strength
                + 0.7 * (1.0 - legitimacy)
                + 0.6 * symbolic_gap
                + 0.3 * agent.e_state.epistemic_vigilance
            )
        elif action_type == ActionType.SANCTION:
            if not targets:
                return None
            score = (
                1.0 * agent.d_state.role_duty_strength
                + 0.7 * enforcement
                + 0.5 * self._strongest_case_confidence(world)
                - 0.2 * world.institution.capture_pressure
            )
        elif action_type == ActionType.APPEAL:
            if not agent.o_state.pending_appeal:
                return None
            score = 0.8 * agent.d_state.appeal_propensity + 0.3 * (1.0 - legitimacy)
        elif action_type == ActionType.INVEST_E:
            score = (
                0.7 * agent.u_state.fairness
                + 0.6 * evidence_gap
                + 0.4 * agent.u_state.long_term_horizon
                - 0.4 * agent.u_state.greed
            )
        elif action_type == ActionType.INVEST_D:
            score = (
                0.7 * agent.d_state.role_duty_strength
                + 0.6 * symbolic_gap
                + 0.4 * agent.u_state.fairness
                - 0.3 * agent.u_state.greed
            )
        elif action_type == ActionType.DO_NOTHING:
            score = 0.05 + 0.1 * agent.u_state.risk_tolerance
        if status == DeonticStatus.REQUIRED:
            score += 0.65
        elif status == DeonticStatus.CONTESTABLE:
            score -= 0.1
        elif status == DeonticStatus.FORBIDDEN:
            score -= 0.35
        return score

    def _apply_action(self, world: WorldState, action: Action) -> None:
        actor = self._agent_by_id(world, action.actor_id)
        actor.last_action = action.action_type.value
        actor.o_state.resources = max(0.0, actor.o_state.resources - action.material_cost)
        self._apply_lane_impact(actor, action.lane_impact)
        for contract in get_action_contracts(action.action_type):
            self._record_event(
                EventRecordKind.DIAGNOSTIC_NOTE,
                turn=world.turn,
                summary=f"{action.actor_id} consumed {contract.contract_kind.value}",
                related_ids=(action.id, action.actor_id),
            )
        if action.action_type == ActionType.CONTRIBUTE:
            world.resource_pool.stock = clamp(
                world.resource_pool.stock + 2.2, 0.0, world.resource_pool.capacity
            )
        elif action.action_type == ActionType.DEFECT:
            world.resource_pool.stock = clamp(
                world.resource_pool.stock - 2.8 * world.resource_pool.extraction_damage,
                0.0,
                world.resource_pool.capacity,
            )
            actor.o_state.resources += 1.8
            self._emit_violation_evidence(
                world, actor.id, action.id, 0.38 + 0.2 * action.observability
            )
        elif action.action_type == ActionType.SHARE_CLAIM:
            world.claims.append(
                Claim(
                    id=self._next_id("claim"),
                    turn=world.turn,
                    source_id=actor.id,
                    proposition="commons_stock",
                    value=round(actor.e_state.belief_commons, 4),
                    confidence=clamp(1.0 - actor.e_state.uncertainty),
                    truthful=True,
                    audience=("public_archive",),
                )
            )
        elif action.action_type == ActionType.MISREPORT:
            distorted = clamp(
                actor.e_state.belief_commons + 18.0, 0.0, world.resource_pool.capacity
            )
            world.claims.append(
                Claim(
                    id=self._next_id("claim"),
                    turn=world.turn,
                    source_id=actor.id,
                    proposition="commons_stock",
                    value=round(distorted, 4),
                    confidence=clamp(0.45 + actor.u_state.greed * 0.25),
                    truthful=False,
                    audience=("public_archive",),
                )
            )
            self._emit_violation_evidence(world, actor.id, action.id, 0.42)
        elif action.action_type == ActionType.VERIFY:
            world.evidence_records.append(
                EvidenceRecord(
                    id=self._next_id("ev"),
                    turn=world.turn,
                    kind="verification_record",
                    proposition="commons_stock",
                    value=round(world.resource_pool.stock, 4),
                    confidence=clamp(0.7 + actor.e_state.verification_capacity * 0.25),
                    source_ids=(action.id,),
                    target_agent_id=None,
                )
            )
            actor.e_state.last_verified_turn = world.turn
            actor.e_state.uncertainty = clamp(actor.e_state.uncertainty - 0.18)
            actor.e_state.belief_commons = round(
                0.7 * actor.e_state.belief_commons + 0.3 * world.resource_pool.stock,
                6,
            )
        elif action.action_type == ActionType.AUDIT:
            selective = (
                world.institution.sanction_consistency < 0.45
                or world.institution.capture_pressure > 0.35
            )
            audit = AuditResult(
                id=self._next_id("audit"),
                turn=world.turn,
                auditor_id=actor.id,
                target_institution_id=world.institution.id,
                fairness_score=clamp(
                    0.5 * world.institution.sanction_consistency
                    + 0.3 * world.institution.operativity
                    - 0.3 * world.institution.capture_pressure
                ),
                truth_alignment=clamp(
                    0.4 * world.institution.archive_capacity
                    + 0.3 * world.institution.public_epistemics_level
                    + 0.3 * (1.0 - world.config.misinformation)
                ),
                selective_enforcement_detected=selective,
                notes="Audit sampled recent evidence and sanction consistency.",
            )
            world.audit_results.append(audit)
            if selective:
                world.institution.legitimacy = clamp(world.institution.legitimacy - 0.03)
                world.institution.capture_pressure = clamp(
                    world.institution.capture_pressure + 0.05
                )
            else:
                world.institution.legitimacy = clamp(world.institution.legitimacy + 0.02)
                world.institution.capture_pressure = clamp(
                    world.institution.capture_pressure - 0.03
                )
        elif action.action_type == ActionType.SANCTION:
            if action.targets:
                target = self._agent_by_id(world, action.targets[0])
                target.o_state.resources = max(
                    0.0, target.o_state.resources - world.config.sanction_severity
                )
                target.o_state.sanctioned_last_turn = True
                target.o_state.pending_appeal = world.institution.appeal_availability >= 0.6
                sanction = SanctionEvent(
                    id=self._next_id("san"),
                    turn=world.turn,
                    actor_id=actor.id,
                    target_id=target.id,
                    reason="resource_fine",
                    severity=clamp(world.config.sanction_severity / 3.0),
                    evidence_ref=self._latest_case_id(world, target.id),
                    fair=world.institution.sanction_consistency >= 0.45,
                    appealed=target.o_state.pending_appeal,
                    upheld=not target.o_state.pending_appeal,
                )
                world.sanction_events.append(sanction)
                world.institution.enforcement_remaining = clamp(
                    world.institution.enforcement_remaining - 0.1
                )
                if sanction.fair:
                    world.institution.legitimacy = clamp(world.institution.legitimacy + 0.01)
                    world.institution.operativity = clamp(world.institution.operativity + 0.015)
                else:
                    world.institution.legitimacy = clamp(world.institution.legitimacy - 0.02)
        elif action.action_type == ActionType.APPEAL:
            actor.o_state.pending_appeal = False
            if world.institution.appeal_availability >= 0.65:
                actor.o_state.resources += 0.4
                world.institution.legitimacy = clamp(world.institution.legitimacy + 0.01)
        elif action.action_type == ActionType.INVEST_E:
            world.institution.archive_capacity = clamp(world.institution.archive_capacity + 0.03)
            world.institution.public_epistemics_level = clamp(
                world.institution.public_epistemics_level + 0.035
            )
            for candidate in self._iter_agents(world):
                candidate.e_state.evidence_access = clamp(candidate.e_state.evidence_access + 0.01)
        elif action.action_type == ActionType.INVEST_D:
            world.institution.operativity = clamp(world.institution.operativity + 0.03)
            world.institution.sanction_consistency = clamp(
                world.institution.sanction_consistency + 0.025
            )
            world.institution.enforcement_remaining = clamp(
                world.institution.enforcement_remaining + 0.05
            )

    def _emit_violation_evidence(
        self, world: WorldState, target_agent_id: str, action_id: str, confidence: float
    ) -> None:
        if self.rng.random() > 0.85:
            return
        world.evidence_records.append(
            EvidenceRecord(
                id=self._next_id("ev"),
                turn=world.turn,
                kind="suspected_violation",
                proposition="norm_violation",
                value=1.0,
                confidence=clamp(confidence),
                source_ids=(action_id,),
                target_agent_id=target_agent_id,
            )
        )

    def _emit_public_report(self, world: WorldState) -> None:
        source_type = "ai" if world.config.ai_mode.value != "none" else "institution"
        confidence = clamp(
            0.45
            + 0.25 * world.institution.archive_capacity
            + 0.2 * world.institution.public_epistemics_level
            + 0.1 * world.config.ai_reliability
        )
        if world.config.ai_mode.value == "sycophantic":
            summary_stock = clamp(
                world.resource_pool.stock + 12.0, 0.0, world.resource_pool.capacity
            )
            truthful = False
            bias_note = "sycophantic upward bias"
        else:
            summary_stock = clamp(
                world.resource_pool.stock + self.rng.gauss(0.0, world.config.misinformation * 6.0),
                0.0,
                world.resource_pool.capacity,
            )
            truthful = abs(summary_stock - world.resource_pool.stock) <= 8.0
            bias_note = ""
        reported_violation_rate = clamp(
            len([record for record in world.evidence_records if record.turn == world.turn])
            / max(1, len(world.agents) / 4)
        )
        world.public_reports.append(
            PublicReport(
                id=self._next_id("report"),
                turn=world.turn,
                source_type=source_type,
                summary_stock=round(summary_stock, 4),
                reported_violation_rate=reported_violation_rate,
                confidence=confidence,
                bias_note=bias_note,
                truthful=truthful,
            )
        )

    def _update_epistemics(self, world: WorldState) -> None:
        latest_report = world.public_reports[-1] if world.public_reports else None
        for agent in self._iter_agents(world):
            own_observations = [
                obs
                for obs in world.observations
                if obs.turn == world.turn
                and obs.observer_id == agent.id
                and obs.proposition == "commons_stock"
            ]
            evidence_values = [
                record.value
                for record in world.evidence_records
                if record.turn >= max(0, world.turn - 1) and record.proposition == "commons_stock"
            ]
            weighted_sum = agent.e_state.belief_commons * max(0.15, 1.0 - agent.e_state.uncertainty)
            weight_total = max(0.15, 1.0 - agent.e_state.uncertainty)
            for observation in own_observations:
                weight = (
                    0.35 * observation.confidence * (0.25 + 0.75 * agent.e_state.evidence_access)
                )
                weighted_sum += observation.value * weight
                weight_total += weight
            for evidence_value in evidence_values[-3:]:
                weight = 0.3 * (0.4 + 0.9 * agent.e_state.evidence_access)
                weighted_sum += evidence_value * weight
                weight_total += weight
            if latest_report is not None:
                trust = (
                    agent.e_state.trust_ai
                    if latest_report.source_type == "ai"
                    else agent.e_state.trust_institution
                )
                weight = 0.45 * latest_report.confidence * trust
                weighted_sum += latest_report.summary_stock * weight
                weight_total += weight
                delta = 0.02 if latest_report.truthful else -0.04
                if latest_report.source_type == "ai":
                    agent.e_state.trust_ai = clamp(agent.e_state.trust_ai + delta)
                else:
                    agent.e_state.trust_institution = clamp(agent.e_state.trust_institution + delta)
            new_belief = clamp(
                weighted_sum / max(weight_total, 0.01), 0.0, world.resource_pool.capacity
            )
            discrepancy = (
                abs(new_belief - latest_report.summary_stock) / world.resource_pool.capacity
                if latest_report is not None
                else 0.0
            )
            uncertainty = agent.e_state.uncertainty
            uncertainty += world.config.misinformation * 0.18
            uncertainty += discrepancy * 0.12
            uncertainty -= agent.e_state.verification_capacity * 0.12
            if agent.last_action == ActionType.VERIFY.value:
                uncertainty -= 0.1
            agent.e_state.belief_commons = round(new_belief, 6)
            agent.e_state.uncertainty = clamp(uncertainty, 0.05, 0.95)
            audit_penalty = sum(
                0.05 if audit.selective_enforcement_detected else -0.015
                for audit in world.audit_results[-2:]
            )
            agent.d_state.legitimacy_belief = clamp(
                0.6 * agent.d_state.legitimacy_belief
                + 0.25 * world.institution.legitimacy
                + 0.15 * agent.e_state.trust_institution
                - audit_penalty
            )

    def _apply_lane_impact(self, agent: Agent, lane_impact: LaneDelta) -> None:
        agent.o_state.resources = max(0.0, agent.o_state.resources + 0.1 * lane_impact.O)
        agent.e_state.uncertainty = clamp(agent.e_state.uncertainty - 0.05 * lane_impact.E)
        agent.e_state.trust_institution = clamp(
            agent.e_state.trust_institution + 0.04 * lane_impact.E
        )
        agent.d_state.legitimacy_belief = clamp(
            agent.d_state.legitimacy_belief + 0.05 * lane_impact.D
        )
        agent.d_state.norm_commitment = clamp(
            agent.d_state.norm_commitment + 0.03 * lane_impact.D - 0.02 * max(lane_impact.U, 0.0)
        )
        agent.u_state.greed = clamp(agent.u_state.greed + 0.03 * lane_impact.U)

    def _select_sanction_target(self, world: WorldState) -> str | None:
        candidates = [
            record
            for record in world.evidence_records
            if record.target_agent_id is not None and record.turn >= max(0, world.turn - 2)
        ]
        if not candidates:
            return None
        candidates.sort(key=lambda record: (-record.confidence, record.target_agent_id or ""))
        return candidates[0].target_agent_id

    def _strongest_case_confidence(self, world: WorldState) -> float:
        candidates = [
            record.confidence
            for record in world.evidence_records
            if record.target_agent_id is not None and record.turn >= max(0, world.turn - 2)
        ]
        return max(candidates, default=0.0)

    def _latest_case_id(self, world: WorldState, target_id: str) -> str | None:
        candidates = [
            record
            for record in world.evidence_records
            if record.target_agent_id == target_id and record.turn >= max(0, world.turn - 2)
        ]
        if not candidates:
            return None
        candidates.sort(key=lambda record: (-record.confidence, record.id))
        return candidates[0].id

    def _agent_by_id(self, world: WorldState, agent_id: str) -> Agent:
        for agent in self._iter_agents(world):
            if agent.id == agent_id:
                return agent
        raise KeyError(f"unknown agent: {agent_id}")

    def _iter_agents(self, world: WorldState) -> list[Agent]:
        return sorted(world.agents, key=lambda agent: agent.id)

    def _next_id(self, prefix: str) -> str:
        self._id_counter += 1
        return f"{prefix}_{self._id_counter:05d}"

    def _record_event(
        self,
        event_kind: EventRecordKind,
        *,
        turn: int,
        summary: str,
        related_ids: tuple[str, ...],
        world: WorldState | None = None,
    ) -> None:
        target_world = world if world is not None else self.state
        if target_world is None:
            return
        target_world.event_records.append(
            EventRecord(
                event_kind=event_kind,
                turn=turn,
                summary=summary,
                related_ids=tuple(sorted(set(related_ids))),
            )
        )


def run_canonical_scenario(
    scenario_name: str, *, seed: int = CANONICAL_REPLAY_SEED, steps: int = CANONICAL_REPLAY_HORIZON
) -> WorldState:
    simulation = ODEUSimulation()
    simulation.reset(scenario_name, seed=seed)
    simulation.run(steps=steps)
    return simulation.get_state()


def summarize_action_counts(world: WorldState) -> dict[str, int]:
    counts = Counter(action.action_type.value for action in world.planned_actions)
    return {name: counts[name] for name in sorted(counts)}


def summarize_lane_state(world: WorldState) -> dict[str, float]:
    if not world.agents:
        raise ValueError("world.agents must be non-empty")
    return {
        "mean_legitimacy_belief": round(
            mean(agent.d_state.legitimacy_belief for agent in world.agents), 6
        ),
        "mean_uncertainty": round(mean(agent.e_state.uncertainty for agent in world.agents), 6),
        "mean_resources": round(mean(agent.o_state.resources for agent in world.agents), 6),
    }
