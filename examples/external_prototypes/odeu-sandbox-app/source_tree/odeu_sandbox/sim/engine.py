from __future__ import annotations

import random
from collections import Counter
from statistics import mean
from typing import Iterable

from .actions import ACTION_LIBRARY, get_action_template
from .metrics import clamp, compute_metrics
from .models import (
    AIBiasMode,
    Action,
    ActionType,
    Agent,
    Archetype,
    AuditResult,
    Claim,
    DState,
    DeonticStatus,
    EState,
    EvidenceRecord,
    Institution,
    LaneDelta,
    Norm,
    NormModality,
    OState,
    Observation,
    PublicReport,
    ResourcePool,
    SanctionEvent,
    ScenarioConfig,
    UState,
    WorldState,
)
from .scenarios import DEFAULT_SCENARIO_NAME, get_scenario


class ODEUSimulation:
    def __init__(self) -> None:
        self.rng = random.Random(1)
        self._id_counter = 0
        self.state: WorldState | None = None
        self.reset(DEFAULT_SCENARIO_NAME, seed=1)

    # ------------------------------------------------------------------
    # public API
    # ------------------------------------------------------------------
    def reset(self, scenario_name: str = DEFAULT_SCENARIO_NAME, seed: int = 1, overrides: dict | None = None) -> WorldState:
        self.rng = random.Random(seed)
        self._id_counter = 0
        config = get_scenario(scenario_name)
        if overrides:
            payload = config.model_dump(mode='python')
            payload.update(overrides)
            config = ScenarioConfig.model_validate(payload)
        self.state = self._build_world(config=config, seed=seed)
        metric = compute_metrics(self.state)
        self.state.metrics_history = [metric]
        self.state.last_run_summary = self._build_lane_summary()
        return self.state

    def step(self, steps: int = 1) -> WorldState:
        for _ in range(max(1, steps)):
            if not self.state:
                raise RuntimeError("Simulation not initialized")
            self._step_once()
        if not self.state:
            raise RuntimeError("Simulation missing after step")
        return self.state

    def get_state(self) -> WorldState:
        if not self.state:
            raise RuntimeError("Simulation not initialized")
        return self.state

    # ------------------------------------------------------------------
    # construction
    # ------------------------------------------------------------------
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
        norms = self._build_norms()
        agents = self._build_agents(config, resource_pool, institution)
        world = WorldState(
            seed=seed,
            scenario=config.name,
            config=config,
            resource_pool=resource_pool,
            institution=institution,
            norms=norms,
            agents=agents,
            event_log=[f"Initialized scenario {config.name} with seed {seed}."],
        )
        # initial public report so epistemics has a starting surface
        initial_reports = self._generate_public_reports(world)
        world.pending_public_reports.extend(initial_reports)
        return world

    def _build_norms(self) -> list[Norm]:
        return [
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

    def _build_agents(self, config: ScenarioConfig, resource_pool: ResourcePool, institution: Institution) -> list[Agent]:
        counts = self._resolve_archetype_counts(config)
        agents: list[Agent] = []
        all_slots: list[Archetype] = (
            [Archetype.COOPERATOR] * counts[Archetype.COOPERATOR]
            + [Archetype.OPPORTUNIST] * counts[Archetype.OPPORTUNIST]
            + [Archetype.AUDITOR] * counts[Archetype.AUDITOR]
            + [Archetype.OFFICIAL] * counts[Archetype.OFFICIAL]
            + [Archetype.AI_DEPENDENT] * counts[Archetype.AI_DEPENDENT]
        )
        self.rng.shuffle(all_slots)
        ids = [f"agent_{idx:02d}" for idx in range(len(all_slots))]
        neighbor_map = self._build_peer_network(ids)

        for idx, archetype in enumerate(all_slots):
            belief_noise = self.rng.uniform(-10, 10)
            belief = clamp(resource_pool.stock + belief_noise, 0.0, resource_pool.capacity)
            uncertainty = clamp(0.35 + config.misinformation * 0.4 + self.rng.uniform(-0.08, 0.08))
            base_income = self.rng.uniform(0.8, 1.25)

            if archetype == Archetype.COOPERATOR:
                greed = self.rng.uniform(0.18, 0.38)
                fairness = self.rng.uniform(0.68, 0.9)
                horizon = self.rng.uniform(0.6, 0.88)
                risk = self.rng.uniform(0.2, 0.5)
                sanction_aversion = self.rng.uniform(0.55, 0.8)
                norm_commitment = self.rng.uniform(0.7, 0.92)
                role_duty = self.rng.uniform(0.15, 0.35)
                evidence_access = self.rng.uniform(0.45, 0.65)
                verification = clamp(config.verification_capacity + self.rng.uniform(-0.05, 0.08))
                vigilance = self.rng.uniform(0.45, 0.68)
                resources = self.rng.uniform(4.5, 7.0)
            elif archetype == Archetype.OPPORTUNIST:
                greed = self.rng.uniform(0.65, 0.95)
                fairness = self.rng.uniform(0.08, 0.3)
                horizon = self.rng.uniform(0.15, 0.45)
                risk = self.rng.uniform(0.55, 0.9)
                sanction_aversion = self.rng.uniform(0.15, 0.45)
                norm_commitment = self.rng.uniform(0.1, 0.35)
                role_duty = self.rng.uniform(0.05, 0.2)
                evidence_access = self.rng.uniform(0.25, 0.45)
                verification = clamp(config.verification_capacity + self.rng.uniform(-0.15, 0.03))
                vigilance = self.rng.uniform(0.1, 0.28)
                resources = self.rng.uniform(4.5, 7.5)
            elif archetype == Archetype.AUDITOR:
                greed = self.rng.uniform(0.18, 0.35)
                fairness = self.rng.uniform(0.58, 0.82)
                horizon = self.rng.uniform(0.45, 0.8)
                risk = self.rng.uniform(0.25, 0.55)
                sanction_aversion = self.rng.uniform(0.45, 0.72)
                norm_commitment = self.rng.uniform(0.62, 0.88)
                role_duty = self.rng.uniform(0.55, 0.85)
                evidence_access = self.rng.uniform(0.62, 0.85)
                verification = clamp(config.verification_capacity + self.rng.uniform(0.08, 0.18))
                vigilance = self.rng.uniform(0.75, 0.95)
                resources = self.rng.uniform(4.0, 6.5)
            elif archetype == Archetype.OFFICIAL:
                greed = self.rng.uniform(0.25, 0.45)
                fairness = self.rng.uniform(0.5, 0.78)
                horizon = self.rng.uniform(0.48, 0.82)
                risk = self.rng.uniform(0.18, 0.45)
                sanction_aversion = self.rng.uniform(0.42, 0.68)
                norm_commitment = self.rng.uniform(0.6, 0.88)
                role_duty = self.rng.uniform(0.82, 0.98)
                evidence_access = self.rng.uniform(0.5, 0.72)
                verification = clamp(config.verification_capacity + self.rng.uniform(0.02, 0.12))
                vigilance = self.rng.uniform(0.55, 0.78)
                resources = self.rng.uniform(4.5, 6.8)
            else:
                greed = self.rng.uniform(0.32, 0.55)
                fairness = self.rng.uniform(0.35, 0.6)
                horizon = self.rng.uniform(0.4, 0.72)
                risk = self.rng.uniform(0.35, 0.58)
                sanction_aversion = self.rng.uniform(0.4, 0.7)
                norm_commitment = self.rng.uniform(0.38, 0.65)
                role_duty = self.rng.uniform(0.15, 0.3)
                evidence_access = self.rng.uniform(0.28, 0.48)
                verification = clamp(config.verification_capacity + self.rng.uniform(-0.08, 0.05))
                vigilance = self.rng.uniform(0.25, 0.45)
                resources = self.rng.uniform(4.2, 6.8)

            peer_trust = {
                neighbor: self.rng.uniform(0.35, 0.75)
                for neighbor in neighbor_map[ids[idx]]
            }
            trust_ai = 0.2 if config.ai_mode == AIBiasMode.NONE else self.rng.uniform(0.4, 0.9)
            if archetype == Archetype.AI_DEPENDENT:
                trust_ai = max(trust_ai, self.rng.uniform(0.75, 0.95))

            agent = Agent(
                id=ids[idx],
                archetype=archetype,
                o_state=OState(
                    resources=resources,
                    base_income=base_income,
                    evidence_access=evidence_access,
                ),
                e_state=EState(
                    belief_commons=belief,
                    uncertainty=uncertainty,
                    evidence_access=evidence_access,
                    verification_capacity=verification,
                    epistemic_vigilance=vigilance,
                    trust_institution=clamp(institution.legitimacy + self.rng.uniform(-0.18, 0.12)),
                    trust_ai=clamp(trust_ai),
                    peer_trust=peer_trust,
                ),
                d_state=DState(
                    norm_commitment=norm_commitment,
                    legitimacy_belief=clamp(institution.legitimacy + self.rng.uniform(-0.12, 0.08)),
                    role_duty_strength=role_duty,
                    appeal_propensity=self.rng.uniform(0.35, 0.8),
                    compliance_bias=clamp((norm_commitment + fairness) / 2),
                ),
                u_state=UState(
                    greed=greed,
                    long_term_horizon=horizon,
                    fairness=fairness,
                    risk_tolerance=risk,
                    sanction_aversion=sanction_aversion,
                ),
            )
            agents.append(agent)
        return agents

    def _resolve_archetype_counts(self, config: ScenarioConfig) -> dict[Archetype, int]:
        weights = {
            Archetype.COOPERATOR: config.cooperator_share,
            Archetype.OPPORTUNIST: config.opportunist_share,
            Archetype.AUDITOR: config.auditor_share,
            Archetype.OFFICIAL: config.official_share,
            Archetype.AI_DEPENDENT: config.ai_dependent_share,
        }
        counts = {arch: int(config.num_agents * share) for arch, share in weights.items()}
        while sum(counts.values()) < config.num_agents:
            target = max(weights, key=weights.get)
            counts[target] += 1
            weights[target] = max(0.0, weights[target] - 0.01)
        while sum(counts.values()) > config.num_agents:
            target = max(counts, key=counts.get)
            if counts[target] > 1:
                counts[target] -= 1
            else:
                break
        return counts

    def _build_peer_network(self, ids: list[str]) -> dict[str, list[str]]:
        n = len(ids)
        adjacency = {agent_id: set() for agent_id in ids}
        for idx, agent_id in enumerate(ids):
            adjacency[agent_id].add(ids[(idx - 1) % n])
            adjacency[agent_id].add(ids[(idx + 1) % n])
        extra_edges = max(1, n // 3)
        for _ in range(extra_edges):
            left, right = self.rng.sample(ids, 2)
            adjacency[left].add(right)
            adjacency[right].add(left)
        return {agent_id: sorted(neighbors) for agent_id, neighbors in adjacency.items()}

    # ------------------------------------------------------------------
    # core turn loop
    # ------------------------------------------------------------------
    def _step_once(self) -> None:
        world = self.get_state()
        world.turn += 1
        world.planned_actions = []
        world.audit_results = [a for a in world.audit_results if a.turn >= world.turn - 12]
        world.sanction_events = [s for s in world.sanction_events if s.turn >= world.turn - 12]

        self.update_ontology(world)
        self.observe_world(world)
        self.update_epistemics(world)
        planned = self.plan_actions(world)
        world.planned_actions = planned
        self.resolve_actions(world, planned)
        self.update_deontics(world)
        metric = compute_metrics(world)
        world.metrics_history.append(metric)
        world.last_run_summary = self._build_lane_summary()
        self._trim_buffers(world)

    # ------------------------------------------------------------------
    # Phase 1: O / world update
    # ------------------------------------------------------------------
    def update_ontology(self, world: WorldState) -> None:
        commons = world.resource_pool
        commons.stock = clamp(
            commons.stock + commons.regeneration_rate * (commons.capacity - commons.stock),
            0.0,
            commons.capacity,
        )
        world.institution.enforcement_remaining = max(
            0.0,
            world.institution.enforcement_capacity * (0.45 + 0.55 * world.institution.operativity),
        )
        for agent in world.agents:
            agent.o_state.resources += agent.o_state.base_income
            if agent.o_state.sanctioned_last_turn:
                agent.o_state.resources = max(0.0, agent.o_state.resources - 0.2)
                agent.o_state.sanctioned_last_turn = False
        self._log(world, f"Turn {world.turn}: commons regenerated to {commons.stock:.1f} / {commons.capacity:.0f}.")

    # ------------------------------------------------------------------
    # Phase 2: observation and signal generation
    # ------------------------------------------------------------------
    def observe_world(self, world: WorldState) -> None:
        world.observations = list(world.pending_observations)
        world.pending_observations = []
        world.claims.extend(world.pending_claims)
        world.pending_claims = []
        world.public_reports.extend(world.pending_public_reports)
        world.pending_public_reports = []
        world.evidence_records.extend(world.pending_evidence)
        world.pending_evidence = []

        for agent in world.agents:
            agent.recent_observations = []
            signal_noise = (0.12 + world.config.misinformation * 0.25) * world.resource_pool.capacity
            signal_noise *= 1.1 - 0.4 * agent.e_state.evidence_access
            observed = clamp(world.resource_pool.stock + self.rng.gauss(0, signal_noise), 0.0, world.resource_pool.capacity)
            confidence = clamp(1.0 - signal_noise / world.resource_pool.capacity)
            obs = Observation(
                id=self._next_id("obs"),
                turn=world.turn,
                observer_id=agent.id,
                kind="local_stock_trace",
                proposition="commons_stock",
                value=observed,
                confidence=confidence,
                raw_text=f"Local commons signal {observed:.1f}",
            )
            world.observations.append(obs)
            agent.recent_observations.append(obs.id)

        for obs in world.observations:
            for agent in world.agents:
                if agent.id == obs.observer_id:
                    continue
                if obs.observer_id in agent.e_state.peer_trust and self.rng.random() < 0.18:
                    agent.recent_observations.append(obs.id)

    # ------------------------------------------------------------------
    # Phase 3: E update
    # ------------------------------------------------------------------
    def update_epistemics(self, world: WorldState) -> None:
        recent_reports = [report for report in world.public_reports if report.turn >= world.turn - 2]
        recent_claims = [claim for claim in world.claims if claim.turn >= world.turn - 2]
        recent_evidence = [record for record in world.evidence_records if record.turn >= world.turn - 3 and record.archived]
        recent_audits = [audit for audit in world.audit_results if audit.turn >= world.turn - 3]

        for agent in world.agents:
            local_obs = [obs for obs in world.observations if obs.observer_id == agent.id and obs.proposition == "commons_stock"]
            accessible_claims = [claim for claim in recent_claims if agent.id in claim.audience]
            accessible_evidence = [ev for ev in recent_evidence if self.rng.random() < (0.4 + 0.5 * agent.e_state.evidence_access)]

            weighted_sum = agent.e_state.belief_commons * max(0.15, 1.0 - agent.e_state.uncertainty)
            weight_total = max(0.15, 1.0 - agent.e_state.uncertainty)

            for obs in local_obs:
                weight = 0.3 * obs.confidence * (0.25 + 0.75 * agent.e_state.evidence_access)
                weighted_sum += obs.value * weight
                weight_total += weight

            for report in recent_reports:
                trust = agent.e_state.trust_ai if report.source_type == "ai" else agent.e_state.trust_institution
                weight = 0.55 * report.confidence * trust * (0.45 + 0.85 * (1.0 - agent.e_state.evidence_access) + (0.25 if agent.archetype == Archetype.AI_DEPENDENT else 0.0))
                weighted_sum += report.summary_stock * weight
                weight_total += weight
                if report.truthful is not None:
                    delta = 0.03 if report.truthful else -0.05
                    if report.source_type == "ai":
                        agent.e_state.trust_ai = clamp(agent.e_state.trust_ai + delta)
                    else:
                        agent.e_state.trust_institution = clamp(agent.e_state.trust_institution + delta)

            for claim in accessible_claims:
                trust = agent.e_state.peer_trust.get(claim.source_id, 0.35)
                weight = 0.32 * claim.confidence * trust * (0.6 + 0.5 * world.config.misinformation)
                weighted_sum += claim.value * weight
                weight_total += weight
                if claim.truthful is not None and claim.source_id in agent.e_state.peer_trust:
                    agent.e_state.peer_trust[claim.source_id] = clamp(
                        agent.e_state.peer_trust[claim.source_id] + (0.025 if claim.truthful else -0.04)
                    )

            for record in accessible_evidence:
                if record.proposition == "commons_stock":
                    weight = 0.34 * record.confidence * (0.4 + 0.9 * agent.e_state.evidence_access)
                    weighted_sum += record.value * weight
                    weight_total += weight

            new_belief = clamp(weighted_sum / max(weight_total, 0.01), 0.0, world.resource_pool.capacity)
            discrepancy = 0.0
            if recent_reports:
                discrepancy = abs(new_belief - recent_reports[-1].summary_stock) / world.resource_pool.capacity
            uncertainty = agent.e_state.uncertainty
            uncertainty += world.config.misinformation * 0.18
            uncertainty += discrepancy * 0.15
            uncertainty -= agent.e_state.verification_capacity * 0.12
            uncertainty -= min(0.15, len(accessible_evidence) * 0.015)
            if agent.last_action == ActionType.VERIFY.value or agent.last_action == ActionType.AUDIT.value:
                uncertainty -= 0.1
            agent.e_state.belief_commons = new_belief
            agent.e_state.uncertainty = clamp(uncertainty, 0.05, 0.95)

            audit_penalty = 0.0
            for audit in recent_audits:
                audit_penalty += 0.05 if audit.selective_enforcement_detected else -0.015
            agent.d_state.legitimacy_belief = clamp(
                0.6 * agent.d_state.legitimacy_belief
                + 0.25 * world.institution.legitimacy
                + 0.15 * agent.e_state.trust_institution
                - audit_penalty
            )
        self._log(world, "Epistemic update completed: agents revised commons beliefs and source trust.")

    # ------------------------------------------------------------------
    # Phase 4+5: Deontic evaluation + O/E/D/U-gated decisions
    # ------------------------------------------------------------------
    def plan_actions(self, world: WorldState) -> list[Action]:
        planned: list[Action] = []
        for agent in world.agents:
            candidates = self._generate_candidates(agent, world)
            candidates = self._apply_epistemic_gate(agent, world, candidates)
            candidates = self._apply_deontic_gate(agent, world, candidates)
            action = self.rank_by_utility(agent, world, candidates)
            planned.append(action)
            agent.last_action = action.action_type.value
        return planned

    def _generate_candidates(self, agent: Agent, world: WorldState) -> list[Action]:
        candidates: list[Action] = []
        for action_type, template in ACTION_LIBRARY.items():
            if not self._is_eligible(agent, action_type):
                continue
            if agent.o_state.resources < template.material_cost:
                continue
            if action_type == ActionType.SANCTION and not world.pending_cases:
                continue
            if action_type == ActionType.APPEAL and not agent.o_state.pending_appeal:
                continue
            candidates.append(
                Action(
                    id=self._next_id("act"),
                    turn=world.turn,
                    actor_id=agent.id,
                    action_type=action_type,
                    material_cost=template.material_cost,
                    observability=template.observability,
                    evidence_emission=template.evidence_emission,
                    deontic_status=template.base_deontic_status,
                    lane_impact=template.lane_impact.model_copy(deep=True),
                )
            )
        return candidates

    def _is_eligible(self, agent: Agent, action_type: ActionType) -> bool:
        if action_type in {ActionType.AUDIT}:
            return agent.archetype in {Archetype.AUDITOR, Archetype.OFFICIAL}
        if action_type == ActionType.SANCTION:
            return agent.archetype == Archetype.OFFICIAL
        return True

    def _apply_epistemic_gate(self, agent: Agent, world: WorldState, candidates: list[Action]) -> list[Action]:
        if not candidates:
            return []
        if agent.e_state.uncertainty > 0.72 and agent.e_state.epistemic_vigilance > 0.5:
            keep = [a for a in candidates if a.action_type in {ActionType.VERIFY, ActionType.AUDIT, ActionType.SHARE_CLAIM, ActionType.DO_NOTHING}]
            if keep:
                return keep
        if agent.e_state.belief_commons < 25 and any(a.action_type == ActionType.DEFECT for a in candidates):
            # agents that truly believe the commons is collapsing rarely consider overextraction unless very greedy
            if agent.u_state.greed < 0.75 or agent.e_state.uncertainty < 0.5:
                candidates = [a for a in candidates if a.action_type != ActionType.DEFECT]
        return candidates

    def evaluate_deontics(self, agent: Agent, world: WorldState, action: Action) -> DeonticStatus:
        symbolic_gap = world.institution.formal_presence - world.institution.operativity
        belief_ratio = agent.e_state.belief_commons / world.resource_pool.capacity
        if action.action_type == ActionType.DEFECT:
            return DeonticStatus.FORBIDDEN
        if action.action_type == ActionType.MISREPORT:
            return DeonticStatus.FORBIDDEN
        if action.action_type == ActionType.CONTRIBUTE:
            if belief_ratio < 0.55:
                return DeonticStatus.REQUIRED
            return DeonticStatus.PERMITTED
        if action.action_type == ActionType.VERIFY:
            if agent.e_state.uncertainty > 0.62 and agent.e_state.epistemic_vigilance > 0.55:
                return DeonticStatus.REQUIRED
            return DeonticStatus.PERMITTED
        if action.action_type == ActionType.AUDIT:
            if agent.archetype in {Archetype.AUDITOR, Archetype.OFFICIAL} and (
                world.institution.legitimacy < 0.55
                or world.institution.sanction_consistency < 0.45
                or symbolic_gap > 0.35
            ):
                return DeonticStatus.REQUIRED
            return DeonticStatus.PERMITTED
        if action.action_type == ActionType.SANCTION:
            strongest_case = max((case.confidence for case in world.pending_cases), default=0.0)
            if strongest_case >= 0.42:
                return DeonticStatus.REQUIRED
            return DeonticStatus.CONTESTABLE
        if action.action_type == ActionType.APPEAL:
            return DeonticStatus.PERMITTED
        if action.action_type == ActionType.INVEST_E and world.institution.archive_capacity < 0.3:
            return DeonticStatus.REQUIRED if agent.archetype == Archetype.OFFICIAL else DeonticStatus.PERMITTED
        if action.action_type == ActionType.INVEST_D and world.institution.operativity < 0.38:
            return DeonticStatus.REQUIRED if agent.archetype == Archetype.OFFICIAL else DeonticStatus.PERMITTED
        return DeonticStatus.PERMITTED

    def _apply_deontic_gate(self, agent: Agent, world: WorldState, candidates: list[Action]) -> list[Action]:
        allowed: list[Action] = []
        required: list[Action] = []
        normative_force = agent.d_state.norm_commitment * agent.d_state.legitimacy_belief * max(0.1, world.institution.operativity)
        sanction_force = (world.institution.operativity * world.institution.sanction_consistency + 0.15 * world.config.sanction_severity) * agent.u_state.sanction_aversion
        role_force = agent.d_state.role_duty_strength if agent.archetype == Archetype.OFFICIAL else 0.0
        for action in candidates:
            status = self.evaluate_deontics(agent, world, action)
            action.deontic_status = status
            if status == DeonticStatus.REQUIRED:
                required.append(action)
                continue
            if status == DeonticStatus.FORBIDDEN:
                violation_tolerance = agent.u_state.risk_tolerance + agent.u_state.greed * 0.35
                if normative_force + sanction_force + role_force >= violation_tolerance:
                    continue
                action.deontic_status = DeonticStatus.CONTESTABLE
                allowed.append(action)
                continue
            allowed.append(action)
        if required and (normative_force + role_force) > 0.35:
            return required + [a for a in allowed if a.action_type == ActionType.VERIFY]
        return allowed or [a for a in candidates if a.action_type == ActionType.DO_NOTHING]

    def rank_by_utility(self, agent: Agent, world: WorldState, candidates: list[Action]) -> Action:
        if not candidates:
            template = get_action_template(ActionType.DO_NOTHING)
            return Action(
                id=self._next_id("act"),
                turn=world.turn,
                actor_id=agent.id,
                action_type=ActionType.DO_NOTHING,
                material_cost=template.material_cost,
                observability=template.observability,
                evidence_emission=template.evidence_emission,
                deontic_status=DeonticStatus.PERMITTED,
                lane_impact=template.lane_impact,
                rationale="fallback",
            )
        belief_ratio = agent.e_state.belief_commons / world.resource_pool.capacity
        scarcity_pressure = 1.0 - belief_ratio
        need_pressure = clamp((2.4 - agent.o_state.resources) / 2.4)
        detection_base = 0.35 + 0.65 * world.institution.archive_capacity
        epistemic_surface = 0.35 + 0.65 * world.institution.public_epistemics_level
        pending_case_strength = max((case.confidence for case in world.pending_cases), default=0.0)
        symbolic_gap = world.institution.formal_presence - world.institution.operativity

        scored: list[tuple[float, Action, str]] = []
        for action in candidates:
            expected_detection = action.observability * detection_base * epistemic_surface + 0.18 * world.institution.enforcement_capacity * min(1.0, world.config.sanction_severity / 2.5)
            score = 0.0
            why = ""
            if action.action_type == ActionType.CONTRIBUTE:
                score = (
                    1.35 * agent.u_state.fairness
                    + 0.95 * agent.u_state.long_term_horizon
                    + 0.65 * agent.d_state.legitimacy_belief
                    + 0.7 * scarcity_pressure
                    - 0.75 * agent.u_state.greed
                    - 0.18 * action.material_cost
                )
                why = "commons duty + fairness"
            elif action.action_type == ActionType.DEFECT:
                score = (
                    1.55 * agent.u_state.greed
                    + 0.85 * need_pressure
                    + 0.45 * agent.u_state.risk_tolerance
                    - 1.65 * expected_detection * agent.u_state.sanction_aversion
                    - 1.1 * scarcity_pressure
                    - 0.45 * agent.d_state.norm_commitment
                )
                why = "private gain vs detection"
            elif action.action_type == ActionType.SHARE_CLAIM:
                report_gap = 0.0
                if world.public_reports:
                    report_gap = abs(agent.e_state.belief_commons - world.public_reports[-1].summary_stock) / world.resource_pool.capacity
                score = (
                    0.55 * agent.u_state.fairness
                    + 0.9 * report_gap
                    + 0.45 * (1.0 - agent.e_state.uncertainty)
                    + 0.25 * agent.e_state.epistemic_vigilance
                )
                why = "broadcast local model"
            elif action.action_type == ActionType.MISREPORT:
                score = (
                    0.95 * agent.u_state.greed
                    + 0.8 * world.config.misinformation
                    + 0.35 * symbolic_gap
                    - 1.05 * agent.u_state.fairness
                    - 0.9 * expected_detection * agent.u_state.sanction_aversion
                )
                why = "shape beliefs opportunistically"
            elif action.action_type == ActionType.VERIFY:
                score = (
                    1.2 * agent.e_state.epistemic_vigilance
                    + 1.3 * agent.e_state.uncertainty
                    + (0.45 if agent.archetype == Archetype.AUDITOR else 0.0)
                    - 0.2 * action.material_cost
                )
                why = "uncertainty reduction"
            elif action.action_type == ActionType.AUDIT:
                score = (
                    0.85 * agent.d_state.role_duty_strength
                    + 0.75 * agent.u_state.fairness
                    + 0.7 * max(0.0, 0.6 - world.institution.legitimacy)
                    + 0.55 * symbolic_gap
                )
                why = "inspect institution"
            elif action.action_type == ActionType.SANCTION:
                score = (
                    1.05 * agent.d_state.role_duty_strength
                    + 1.0 * pending_case_strength
                    + 0.45 * world.institution.legitimacy
                    + 0.25 * world.institution.operativity
                )
                why = "official duty"
            elif action.action_type == ActionType.APPEAL:
                score = 1.0 * agent.d_state.appeal_propensity + 0.35 * agent.u_state.fairness
                why = "contest recent sanction"
            elif action.action_type == ActionType.INVEST_E:
                score = (
                    0.65 * agent.u_state.fairness
                    + 0.8 * agent.u_state.long_term_horizon
                    + 0.95 * max(0.0, 0.45 - world.institution.archive_capacity)
                    + 0.8 * max(0.0, 0.45 - world.institution.public_epistemics_level)
                    - 0.45 * agent.u_state.greed
                )
                why = "strengthen evidence infrastructure"
            elif action.action_type == ActionType.INVEST_D:
                score = (
                    0.55 * agent.u_state.fairness
                    + 0.75 * agent.u_state.long_term_horizon
                    + 0.85 * agent.d_state.role_duty_strength
                    + 1.0 * max(0.0, 0.45 - world.institution.operativity)
                    - 0.35 * agent.u_state.greed
                )
                why = "strengthen institution"
            else:
                score = 0.12 + 0.25 * need_pressure + 0.18 * agent.u_state.risk_tolerance
                why = "stand pat"
            score += self.rng.uniform(0.0, 0.03)
            scored.append((score, action, why))
        score, chosen, why = max(scored, key=lambda item: item[0])
        chosen.rationale = f"{why}; utility_score={score:.2f}; deontic={chosen.deontic_status.value}"
        return chosen

    # ------------------------------------------------------------------
    # Phase 6: resolve actions and emit traces
    # ------------------------------------------------------------------
    def resolve_actions(self, world: WorldState, planned: list[Action]) -> None:
        by_type_order = [
            ActionType.CONTRIBUTE,
            ActionType.DEFECT,
            ActionType.INVEST_E,
            ActionType.INVEST_D,
            ActionType.SHARE_CLAIM,
            ActionType.MISREPORT,
            ActionType.VERIFY,
            ActionType.AUDIT,
            ActionType.SANCTION,
            ActionType.APPEAL,
            ActionType.DO_NOTHING,
        ]
        actions_sorted = sorted(planned, key=lambda a: by_type_order.index(a.action_type))
        action_lookup = {action.actor_id: action for action in planned}

        for action in actions_sorted:
            agent = self._agent_by_id(world, action.actor_id)
            template = get_action_template(action.action_type)
            agent.o_state.resources -= template.material_cost
            if action.action_type == ActionType.CONTRIBUTE:
                delta = 1.0 + 0.4 * agent.u_state.fairness
                world.resource_pool.stock = clamp(world.resource_pool.stock + delta, 0.0, world.resource_pool.capacity)
                agent.reputation = clamp(agent.reputation + 0.04)
                self._emit_material_trace(world, agent, action, proposition="commons_stock", value=world.resource_pool.stock)
            elif action.action_type == ActionType.DEFECT:
                gain = min(2.1, 1.3 + agent.u_state.greed)
                damage = min(world.resource_pool.stock, 1.6 + 0.5 * world.resource_pool.extraction_damage)
                world.resource_pool.stock = clamp(world.resource_pool.stock - damage, 0.0, world.resource_pool.capacity)
                agent.o_state.resources += gain
                agent.reputation = clamp(agent.reputation - 0.03)
                self._emit_material_trace(world, agent, action, proposition="detected_defection", value=damage, target_id=agent.id)
            elif action.action_type == ActionType.INVEST_E:
                world.institution.public_epistemics_level = clamp(world.institution.public_epistemics_level + 0.045)
                world.institution.archive_capacity = clamp(world.institution.archive_capacity + 0.03)
                world.institution.budget += 0.3
                self._log(world, f"{agent.id} invested in public epistemics.")
            elif action.action_type == ActionType.INVEST_D:
                world.institution.budget += 0.45
                world.institution.operativity = clamp(world.institution.operativity + 0.025)
                self._log(world, f"{agent.id} invested in institutional capacity.")
            elif action.action_type == ActionType.SHARE_CLAIM:
                claim = self._build_claim(world, agent, truthful=True)
                world.pending_claims.append(claim)
                agent.recent_claim_ids.append(claim.id)
            elif action.action_type == ActionType.MISREPORT:
                claim = self._build_claim(world, agent, truthful=False)
                world.pending_claims.append(claim)
                agent.recent_claim_ids.append(claim.id)
                self._emit_material_trace(world, agent, action, proposition="detected_misreport", value=claim.value, target_id=agent.id)
            elif action.action_type == ActionType.VERIFY:
                self._resolve_verify(world, agent)
            elif action.action_type == ActionType.AUDIT:
                self._resolve_audit(world, agent)
            elif action.action_type == ActionType.SANCTION:
                self._resolve_sanction(world, agent)
            elif action.action_type == ActionType.APPEAL:
                self._resolve_appeal(world, agent)
            elif action.action_type == ActionType.DO_NOTHING:
                agent.o_state.resources += 0.15

        world.pending_public_reports.extend(self._generate_public_reports(world))

        counts = Counter(action.action_type for action in planned)
        defect_count = counts[ActionType.DEFECT]
        if defect_count >= max(4, len(world.agents) // 8) and world.institution.archive_capacity < 0.45:
            self._log(world, "Opportunist cluster increased extraction because expected detection fell.")
        if world.audit_results and world.audit_results[-1].selective_enforcement_detected:
            self._log(world, "Audit revealed sanction asymmetry; legitimacy dropped.")
        if world.institution.formal_presence - world.institution.operativity > 0.45:
            self._log(world, "Institution remained formally active but operativity fell below threshold.")
        if world.config.ai_mode == AIBiasMode.SYCOPHANTIC and world.pending_public_reports:
            self._log(world, "AI mediator biased public reports upward, reducing apparent violation rate.")

    def _emit_material_trace(
        self,
        world: WorldState,
        agent: Agent,
        action: Action,
        proposition: str,
        value: float,
        target_id: str | None = None,
    ) -> None:
        detection_probability = self.o_to_e_trace_probability(world, action)
        if self.rng.random() >= detection_probability:
            return
        observers = self._visible_observers(agent)
        confidence = clamp(detection_probability)
        for observer_id in observers:
            obs = Observation(
                id=self._next_id("obs"),
                turn=world.turn,
                observer_id=observer_id,
                source_action_id=action.id,
                kind="emergent_trace",
                proposition=proposition,
                value=value,
                confidence=confidence,
                raw_text=f"Trace of {action.action_type.value} by {agent.id}",
            )
            world.pending_observations.append(obs)
        if self.rng.random() < world.institution.archive_capacity:
            record = EvidenceRecord(
                id=self._next_id("ev"),
                turn=world.turn,
                kind=proposition,
                proposition=proposition,
                value=value,
                confidence=clamp(0.35 + 0.8 * confidence),
                source_ids=[action.id],
                target_agent_id=target_id,
            )
            world.pending_evidence.append(record)
            if proposition in {"detected_defection", "detected_misreport"}:
                world.pending_cases.append(record)

    def o_to_e_trace_probability(self, world: WorldState, action: Action) -> float:
        return clamp(
            action.observability
            * (0.3 + 0.7 * world.institution.archive_capacity)
            * (0.35 + 0.65 * world.institution.public_epistemics_level)
        )

    def _build_claim(self, world: WorldState, agent: Agent, truthful: bool) -> Claim:
        if truthful:
            value = clamp(agent.e_state.belief_commons + self.rng.gauss(0, 4.0), 0.0, world.resource_pool.capacity)
        else:
            bias = 18.0 if world.config.ai_mode != AIBiasMode.SYCOPHANTIC else 12.0
            value = clamp(world.resource_pool.stock + bias, 0.0, world.resource_pool.capacity)
        neighbors = list(agent.e_state.peer_trust.keys())
        audience = neighbors[:]
        truth = abs(value - world.resource_pool.stock) < 12.0
        claim = Claim(
            id=self._next_id("claim"),
            turn=world.turn,
            source_id=agent.id,
            proposition="commons_stock",
            value=value,
            confidence=clamp(0.45 + 0.35 * (1.0 - agent.e_state.uncertainty)),
            truthful=truth if truthful else False,
            audience=audience,
        )
        verb = "shared claim" if truthful else "misreported"
        self._log(world, f"{agent.id} {verb} about commons state.")
        return claim

    def _resolve_verify(self, world: WorldState, agent: Agent) -> None:
        target_claim = next((claim for claim in reversed(world.claims) if agent.id in claim.audience), None)
        proposition = "commons_stock"
        value = world.resource_pool.stock
        notes = "verified commons stock"
        if target_claim and target_claim.proposition == "commons_stock":
            proposition = target_claim.proposition
            notes = f"verified claim from {target_claim.source_id}"
            if target_claim.truthful is False:
                evidence = EvidenceRecord(
                    id=self._next_id("ev"),
                    turn=world.turn,
                    kind="detected_misreport",
                    proposition="detected_misreport",
                    value=target_claim.value,
                    confidence=clamp(0.68 + 0.25 * agent.e_state.verification_capacity),
                    source_ids=[target_claim.id],
                    target_agent_id=target_claim.source_id,
                )
                world.pending_evidence.append(evidence)
                world.pending_cases.append(evidence)
                self._log(world, f"{agent.id} verified a false claim from {target_claim.source_id}.")
        record = EvidenceRecord(
            id=self._next_id("ev"),
            turn=world.turn,
            kind="verification_record",
            proposition=proposition,
            value=value,
            confidence=clamp(0.6 + 0.3 * agent.e_state.verification_capacity),
            source_ids=[],
        )
        world.pending_evidence.append(record)
        agent.e_state.uncertainty = clamp(agent.e_state.uncertainty - 0.12)
        agent.e_state.last_verified_turn = world.turn
        self._log(world, f"{agent.id} verified public evidence ({notes}).")

    def _resolve_audit(self, world: WorldState, agent: Agent) -> None:
        actual_violation_rate = self._actual_violation_rate(world)
        sanction_fairness = mean([1.0 if event.fair else 0.0 for event in world.sanction_events[-8:]]) if world.sanction_events else 0.7
        report_truth = mean([1.0 if report.truthful else 0.0 for report in world.public_reports[-4:]]) if world.public_reports else 0.6
        selective = sanction_fairness < 0.55 or (actual_violation_rate > 0.2 and not world.pending_cases)
        audit = AuditResult(
            id=self._next_id("audit"),
            turn=world.turn,
            auditor_id=agent.id,
            target_institution_id=world.institution.id,
            fairness_score=clamp(sanction_fairness),
            truth_alignment=clamp(report_truth),
            selective_enforcement_detected=selective,
            notes="Selective enforcement detected" if selective else "Institution broadly aligned",
        )
        world.audit_results.append(audit)
        world.pending_public_reports.append(
            PublicReport(
                id=self._next_id("report"),
                turn=world.turn,
                source_type="audit",
                summary_stock=world.resource_pool.stock,
                reported_violation_rate=actual_violation_rate,
                confidence=clamp(0.58 + 0.28 * agent.e_state.verification_capacity),
                bias_note="audit_publication",
                truthful=True,
            )
        )
        self._log(world, f"{agent.id} audited the institution: {audit.notes.lower()}.")

    def _resolve_sanction(self, world: WorldState, agent: Agent) -> None:
        if world.institution.enforcement_remaining < 0.6 or not world.pending_cases:
            return
        case = max(world.pending_cases, key=lambda ev: ev.confidence)
        world.pending_cases.remove(case)
        target = self._agent_by_id(world, case.target_agent_id or agent.id)
        fair = case.kind in {"detected_defection", "detected_misreport"} and case.confidence >= 0.5
        severity = world.config.sanction_severity * (1.0 if fair else 0.7)
        target.o_state.resources = max(0.0, target.o_state.resources - severity)
        target.o_state.sanctioned_last_turn = True
        target.o_state.pending_appeal = world.institution.appeal_availability > 0.25
        world.institution.enforcement_remaining = max(0.0, world.institution.enforcement_remaining - 0.75)
        event = SanctionEvent(
            id=self._next_id("sanction"),
            turn=world.turn,
            actor_id=agent.id,
            target_id=target.id,
            reason=case.kind,
            severity=severity,
            evidence_ref=case.id,
            fair=fair,
        )
        world.sanction_events.append(event)
        self._log(world, f"{agent.id} sanctioned {target.id} for {case.kind}.")

    def _resolve_appeal(self, world: WorldState, agent: Agent) -> None:
        recent = next((event for event in reversed(world.sanction_events) if event.target_id == agent.id and not event.appealed), None)
        if not recent:
            return
        recent.appealed = True
        if not recent.fair and world.institution.appeal_availability > 0.4:
            restored = 0.7 * recent.severity
            agent.o_state.resources += restored
            recent.upheld = False
            world.institution.legitimacy = clamp(world.institution.legitimacy + 0.04)
            self._log(world, f"Appeal by {agent.id} succeeded and restored {restored:.2f} resources.")
        else:
            recent.upheld = True
            world.institution.legitimacy = clamp(world.institution.legitimacy + 0.01)
            self._log(world, f"Appeal by {agent.id} was denied.")
        agent.o_state.pending_appeal = False

    # ------------------------------------------------------------------
    # Phase 7: D update with explicit cross-lane contracts
    # ------------------------------------------------------------------
    def update_deontics(self, world: WorldState) -> None:
        self.e_to_d_legitimacy_contract(world)
        self.u_to_d_pressure_contract(world)
        self.d_to_o_allocation_contract(world)
        if world.institution.formal_presence - world.institution.operativity > 0.42:
            self._log(world, "Institutional surface has become partly symbolic.")

    def e_to_d_legitimacy_contract(self, world: WorldState) -> None:
        recent_audits = [audit for audit in world.audit_results if audit.turn >= world.turn - 2]
        recent_reports = [report for report in world.public_reports if report.turn >= world.turn - 2]
        recent_sanctions = [event for event in world.sanction_events if event.turn >= world.turn - 2]
        audit_truth = mean([audit.truth_alignment for audit in recent_audits]) if recent_audits else 0.6
        audit_fairness = mean([audit.fairness_score for audit in recent_audits]) if recent_audits else world.institution.sanction_consistency
        selective_rate = mean([1.0 if audit.selective_enforcement_detected else 0.0 for audit in recent_audits]) if recent_audits else 0.0
        report_truth = mean([1.0 if report.truthful else 0.0 for report in recent_reports]) if recent_reports else 0.6
        sanction_fairness = mean([1.0 if event.fair else 0.0 for event in recent_sanctions]) if recent_sanctions else 0.7

        world.institution.legitimacy = clamp(
            world.institution.legitimacy
            + 0.08 * (audit_truth - 0.5)
            + 0.07 * (audit_fairness - 0.5)
            + 0.05 * (report_truth - 0.5)
            + 0.04 * (sanction_fairness - 0.5)
            - 0.11 * selective_rate
        )
        world.institution.sanction_consistency = clamp(0.6 * world.institution.sanction_consistency + 0.4 * sanction_fairness)

    def d_to_o_allocation_contract(self, world: WorldState) -> None:
        budget = world.institution.budget
        legitimacy = world.institution.legitimacy
        operativity = world.institution.operativity
        archive_boost = 0.012 * budget * max(0.2, legitimacy)
        enforcement_boost = 0.03 * budget * max(0.2, operativity)
        world.institution.archive_capacity = clamp(world.institution.archive_capacity * 0.995 + archive_boost)
        world.institution.enforcement_capacity = clamp(world.config.enforcement_capacity + enforcement_boost, 0.05, 1.2)
        world.institution.public_epistemics_level = clamp(
            world.institution.public_epistemics_level * 0.995 + 0.015 * budget * legitimacy
        )
        world.institution.budget = clamp(world.institution.budget * 0.98, 0.0, 12.0)
        world.institution.operativity = clamp(
            0.55 * world.institution.operativity
            + 0.2 * world.institution.legitimacy
            + 0.15 * world.institution.sanction_consistency
            + 0.1 * world.institution.archive_capacity
        )

    def u_to_d_pressure_contract(self, world: WorldState) -> None:
        defectors = [agent for agent in world.agents if agent.last_action == ActionType.DEFECT.value]
        if not defectors:
            world.institution.capture_pressure = clamp(world.institution.capture_pressure * 0.96)
            return
        opportunist_gain = mean([agent.o_state.resources for agent in defectors])
        overall = mean([agent.o_state.resources for agent in world.agents])
        gain_ratio = 0.0 if overall <= 0 else max(0.0, (opportunist_gain - overall) / max(overall, 0.1))
        weak_response = 1.0 - world.institution.enforcement_capacity * world.institution.sanction_consistency
        pressure_increment = 0.045 * gain_ratio * weak_response
        world.institution.capture_pressure = clamp(world.institution.capture_pressure + pressure_increment)
        world.institution.operativity = clamp(world.institution.operativity - 0.045 * world.institution.capture_pressure)
        world.institution.legitimacy = clamp(world.institution.legitimacy - 0.025 * world.institution.capture_pressure)

    # ------------------------------------------------------------------
    # public reports / AI mediator
    # ------------------------------------------------------------------
    def _generate_public_reports(self, world: WorldState) -> list[PublicReport]:
        reports: list[PublicReport] = []
        evidence_stock = [ev.value for ev in world.evidence_records[-12:] if ev.proposition == "commons_stock"]
        if evidence_stock:
            inst_stock = mean(evidence_stock)
        else:
            inst_stock = clamp(
                world.resource_pool.stock + self.rng.gauss(0, world.resource_pool.capacity * (0.12 + world.config.misinformation * 0.2)),
                0.0,
                world.resource_pool.capacity,
            )
        reported_violation_rate = self._actual_violation_rate(world)
        if world.institution.enforcement_capacity > 0.75 and world.institution.public_epistemics_level < 0.3:
            inst_stock = clamp(inst_stock + world.resource_pool.capacity * 0.12)
            reported_violation_rate = max(0.0, reported_violation_rate - 0.18)
        if world.institution.capture_pressure > 0.18:
            inst_stock = clamp(inst_stock + world.resource_pool.capacity * 0.08 * world.institution.capture_pressure)
            reported_violation_rate = max(0.0, reported_violation_rate - 0.1 * world.institution.capture_pressure)
        inst_truth = abs(inst_stock - world.resource_pool.stock) < 12.0 and abs(reported_violation_rate - self._actual_violation_rate(world)) < 0.16
        reports.append(
            PublicReport(
                id=self._next_id("report"),
                turn=world.turn,
                source_type="institution",
                summary_stock=clamp(inst_stock, 0.0, world.resource_pool.capacity),
                reported_violation_rate=clamp(reported_violation_rate),
                confidence=clamp(0.42 + 0.4 * world.institution.archive_capacity),
                bias_note="institutional_summary",
                truthful=inst_truth,
            )
        )

        if world.config.ai_mode != AIBiasMode.NONE:
            actual_violation_rate = self._actual_violation_rate(world)
            if world.config.ai_mode == AIBiasMode.ACCURATE:
                noise = world.resource_pool.capacity * (0.05 + (1.0 - world.config.ai_reliability) * 0.12)
                summary_stock = clamp(world.resource_pool.stock + self.rng.gauss(0, noise), 0.0, world.resource_pool.capacity)
                violation_rate = clamp(actual_violation_rate + self.rng.gauss(0, 0.04))
                bias_note = "audit_supporting"
            else:
                upward_bias = world.resource_pool.capacity * (0.16 + 0.22 * (1.0 - world.institution.legitimacy + world.institution.capture_pressure))
                summary_stock = clamp(world.resource_pool.stock + upward_bias, 0.0, world.resource_pool.capacity)
                violation_rate = clamp(actual_violation_rate - 0.18 - 0.16 * world.institution.capture_pressure)
                bias_note = "sycophantic_upward_bias"
            truthful = abs(summary_stock - world.resource_pool.stock) < 10.0 and abs(violation_rate - actual_violation_rate) < 0.15
            reports.append(
                PublicReport(
                    id=self._next_id("report"),
                    turn=world.turn,
                    source_type="ai",
                    summary_stock=summary_stock,
                    reported_violation_rate=violation_rate,
                    confidence=clamp(0.62 + 0.34 * world.config.ai_reliability),
                    bias_note=bias_note,
                    truthful=truthful,
                )
            )
        return reports

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _actual_violation_rate(self, world: WorldState) -> float:
        if not world.planned_actions:
            return 0.0
        violations = sum(1 for action in world.planned_actions if action.action_type in {ActionType.DEFECT, ActionType.MISREPORT})
        return clamp(violations / len(world.planned_actions))

    def _visible_observers(self, agent: Agent) -> list[str]:
        observers = set(agent.e_state.peer_trust.keys())
        observers.add(agent.id)
        return sorted(observers)

    def _agent_by_id(self, world: WorldState, agent_id: str) -> Agent:
        for agent in world.agents:
            if agent.id == agent_id:
                return agent
        raise KeyError(agent_id)

    def _trim_buffers(self, world: WorldState) -> None:
        world.observations = world.observations[-220:]
        world.evidence_records = world.evidence_records[-180:]
        world.claims = world.claims[-140:]
        world.public_reports = world.public_reports[-80:]
        world.event_log = world.event_log[-120:]
        world.pending_cases = world.pending_cases[-40:]

    def _build_lane_summary(self) -> dict:
        world = self.get_state()
        return {
            "O": {
                "commons_stock": round(world.resource_pool.stock, 2),
                "avg_agent_resources": round(mean([a.o_state.resources for a in world.agents]), 2),
                "archive_capacity": round(world.institution.archive_capacity, 3),
                "enforcement_material_capacity": round(world.institution.enforcement_capacity, 3),
            },
            "E": {
                "avg_belief": round(mean([a.e_state.belief_commons for a in world.agents]), 2),
                "avg_uncertainty": round(mean([a.e_state.uncertainty for a in world.agents]), 3),
                "avg_trust_institution": round(mean([a.e_state.trust_institution for a in world.agents]), 3),
                "avg_trust_ai": round(mean([a.e_state.trust_ai for a in world.agents]), 3),
            },
            "D": {
                "legitimacy": round(world.institution.legitimacy, 3),
                "operativity": round(world.institution.operativity, 3),
                "symbolic_gap": round(world.institution.formal_presence - world.institution.operativity, 3),
                "sanction_consistency": round(world.institution.sanction_consistency, 3),
            },
            "U": {
                "avg_greed": round(mean([a.u_state.greed for a in world.agents]), 3),
                "avg_fairness": round(mean([a.u_state.fairness for a in world.agents]), 3),
                "avg_horizon": round(mean([a.u_state.long_term_horizon for a in world.agents]), 3),
                "capture_pressure": round(world.institution.capture_pressure, 3),
            },
        }

    def _log(self, world: WorldState, text: str) -> None:
        world.event_log.append(text)

    def _next_id(self, prefix: str) -> str:
        self._id_counter += 1
        return f"{prefix}_{self._id_counter:05d}"
