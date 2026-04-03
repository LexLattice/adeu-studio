import {
  clampConfidence,
  type BridgeKind,
  type ClaimStatus,
  type DiagnosticKind,
  type DiagnosticSeverity,
  type FragmentSourceKind,
  type FragmentStatus,
  type LaneId,
  LANE_ORDER,
  type ODEUClaimDecomposition,
  type ODEUInferenceBridge,
  type ODEULaneFragment,
  type ODEUSemanticDiagnostic,
  type ODEUVisualProjection,
  type PaperClaimSpan,
  type PaperSemanticSource,
  type PaperSemanticWorkbenchArtifact,
  type ProcessingPipelineMode,
  type WorkbenchDepth,
} from "./schema";

type SamplePaper = {
  paper_id: string;
  title: string;
  authors: string[];
  year: number;
  venue?: string;
  artifact_kind: PaperSemanticSource["artifact_kind"];
  source_text: string;
  source_notes?: string[];
};

type CuratedLaneSpec = {
  short_label: string;
  text: string;
  source_kind?: FragmentSourceKind;
  status?: FragmentStatus;
  confidence?: number;
  warrant?: string;
};

type CuratedDiagnosticSpec = {
  kind: DiagnosticKind;
  severity: DiagnosticSeverity;
  summary: string;
  lane_ids?: LaneId[];
};

type CuratedClaimSpec = {
  key: string;
  anchor: string;
  claim_text: string;
  summary: string;
  confidence?: number;
  explicitness?: FragmentSourceKind;
  status?: ClaimStatus;
  lanes: Partial<Record<LaneId, CuratedLaneSpec[]>>;
  diagnostics?: CuratedDiagnosticSpec[];
  subclaims?: CuratedClaimSpec[];
};

const DEFAULT_PROCESSOR_VERSION = "paper-semantic-mock.v0";
const PLACEHOLDER_CONFIDENCE = 0.28;
const HEURISTIC_PROCESSOR_VERSION = "paper-semantic-heuristic.v0";

export const SAMPLE_PAPERS: SamplePaper[] = [
  {
    paper_id: "attention-is-all-you-need",
    title: "Attention Is All You Need",
    authors: [
      "Ashish Vaswani",
      "Noam Shazeer",
      "Niki Parmar",
      "Jakob Uszkoreit",
      "Llion Jones",
      "Aidan N. Gomez",
      "Łukasz Kaiser",
      "Illia Polosukhin",
    ],
    year: 2017,
    venue: "NeurIPS",
    artifact_kind: "paper.abstract_digest",
    source_notes: [
      "Demo ship uses a concise paraphrase digest rather than the verbatim abstract.",
      "Paste the full abstract in the input lane to inspect source-authored wording locally.",
    ],
    source_text:
      "Sequence transduction systems often relied on recurrent or convolutional layers that process tokens step by step. This paper introduces the Transformer, an encoder-decoder architecture built entirely around attention. Removing recurrence increases parallelism while positional encodings preserve order information. On machine translation benchmarks, the model delivers stronger quality with lower training cost, supporting the claim that attention can serve as the primary sequence modeling mechanism.",
  },
  {
    paper_id: "bert-pre-training",
    title: "BERT: Pre-training of Deep Bidirectional Transformers for Language Understanding",
    authors: [
      "Jacob Devlin",
      "Ming-Wei Chang",
      "Kenton Lee",
      "Kristina Toutanova",
    ],
    year: 2018,
    venue: "NAACL",
    artifact_kind: "paper.abstract_digest",
    source_notes: [
      "Demo ship uses a concise paraphrase digest rather than the verbatim abstract.",
    ],
    source_text:
      "Earlier language models were typically unidirectional or only shallowly bidirectional. BERT pre-trains deep bidirectional representations by masking tokens and predicting them from both left and right context, together with a sentence-level relation objective. The resulting model can be fine-tuned with minimal task-specific changes. It produces strong benchmark results across question answering, natural language inference, and token-level prediction tasks, suggesting that bidirectional pre-training is broadly useful.",
  },
  {
    paper_id: "gpt3-few-shot",
    title: "Language Models are Few-Shot Learners",
    authors: ["Tom B. Brown", "Benjamin Mann", "Nick Ryder", "Melanie Subbiah", "et al."],
    year: 2020,
    venue: "NeurIPS",
    artifact_kind: "paper.abstract_digest",
    source_notes: [
      "Demo ship uses a concise paraphrase digest rather than the verbatim abstract.",
    ],
    source_text:
      "Scaling autoregressive language models continues to improve their behavior on a wide range of tasks. GPT-3 trains a 175-billion-parameter model and shows that many tasks can be steered by prompts and a small number of examples without gradient updates. Across translation, question answering, and cloze-style evaluation, performance is often competitive but still uneven. The paper also surfaces limits around reasoning consistency, calibration, and bias.",
  },
  {
    paper_id: "clip-natural-language-supervision",
    title: "Learning Transferable Visual Models From Natural Language Supervision",
    authors: ["Alec Radford", "Jong Wook Kim", "Chris Hallacy", "Aditya Ramesh", "et al."],
    year: 2021,
    venue: "ICML",
    artifact_kind: "paper.abstract_digest",
    source_notes: [
      "Demo ship uses a concise paraphrase digest rather than the verbatim abstract.",
    ],
    source_text:
      "Training visual systems on internet-scale image and text pairs can produce transferable representations without fixed label taxonomies. CLIP aligns images and language in a shared embedding space, allowing downstream recognition tasks to be expressed as text matching. This yields strong zero-shot transfer on many datasets and reduces dependence on bespoke supervised label sets. The system reframes recognition as a language-conditioned retrieval problem rather than a closed classifier.",
  },
  {
    paper_id: "alphago-search-and-neural-networks",
    title: "Mastering the game of Go with deep neural networks and tree search",
    authors: ["David Silver", "Aja Huang", "Chris J. Maddison", "Arthur Guez", "et al."],
    year: 2016,
    venue: "Nature",
    artifact_kind: "paper.abstract_digest",
    source_notes: [
      "Demo ship uses a concise paraphrase digest rather than the verbatim abstract.",
    ],
    source_text:
      "Deep neural networks can be coupled with Monte Carlo tree search to choose strong moves in Go. Policy networks narrow attention to promising actions and value networks estimate position strength, so search can focus on useful branches. The integrated AlphaGo system defeats a professional human player, indicating that learned evaluation and explicit search can be productively combined in a difficult planning domain. The result depends on combining representation learning with tightly governed lookahead.",
  },
];

const CURATED_SPECS: Record<string, CuratedClaimSpec[]> = {
  "attention-is-all-you-need": [
    {
      key: "c1",
      anchor: "introduces the Transformer",
      claim_text: "The paper introduces the Transformer as an attention-only encoder-decoder architecture.",
      summary: "Architecture claim: attention replaces recurrence as the main sequencing primitive.",
      confidence: 0.94,
      lanes: {
        O: [
          {
            short_label: "Transformer",
            text: "A sequence transduction architecture is defined as an encoder-decoder built around attention rather than recurrent or convolutional state transitions.",
            source_kind: "explicit",
            status: "explicit",
            confidence: 0.95,
            warrant: "Directly stated in the source digest.",
          },
        ],
        E: [
          {
            short_label: "Direct proposal",
            text: "The source explicitly presents the Transformer as the proposed mechanism, not merely a variation on an existing recurrent model.",
            source_kind: "explicit",
            status: "explicit",
            confidence: 0.91,
            warrant: "Proposal language is explicit in the claim span.",
          },
        ],
        D: [
          {
            short_label: "Positional discipline",
            text: "If recurrence is removed, token order must be reintroduced through an alternate structural device such as positional encoding.",
            source_kind: "inferred",
            status: "inferred",
            confidence: 0.71,
            warrant: "The source mentions preserved order information, but the design requirement is reconstructed by inference.",
          },
        ],
        U: [
          {
            short_label: "Parallel training",
            text: "The architecture is shaped to increase throughput and unlock more efficient training behavior while preserving sequence performance.",
            source_kind: "explicit",
            status: "explicit",
            confidence: 0.87,
            warrant: "Parallelism is named as a benefit in the digest.",
          },
        ],
      },
      diagnostics: [
        {
          kind: "implicit_assumption",
          severity: "warning",
          summary: "The paper relies on an inferred bridge from removed recurrence to alternate order-encoding discipline.",
          lane_ids: ["D"],
        },
      ],
      subclaims: [
        {
          key: "c1a",
          anchor: "built entirely around attention",
          claim_text: "Attention is elevated from one component to the central computational substrate.",
          summary: "Subclaim: attention becomes the primary mechanism, not an auxiliary module.",
          confidence: 0.9,
          lanes: {
            O: [
              {
                short_label: "Primary substrate",
                text: "Attention is typed as the central relational operator of the architecture.",
                confidence: 0.92,
              },
            ],
            E: [
              {
                short_label: "Component move",
                text: "The digest states that the architecture is built entirely around attention.",
                confidence: 0.9,
              },
            ],
            U: [
              {
                short_label: "Simplify path",
                text: "Collapsing around one dominant operator simplifies the path from modeling to parallel execution.",
                source_kind: "inferred",
                status: "inferred",
                confidence: 0.63,
              },
            ],
          },
        },
      ],
    },
    {
      key: "c2",
      anchor: "Removing recurrence increases parallelism",
      claim_text: "Removing recurrence increases parallelism while positional encodings preserve order information.",
      summary: "Mechanism claim: parallelism gains depend on a replacement for sequence order encoding.",
      confidence: 0.91,
      lanes: {
        O: [
          {
            short_label: "No recurrence",
            text: "The model excludes stepwise recurrent state updates from its main sequence mechanism.",
            confidence: 0.91,
          },
        ],
        E: [
          {
            short_label: "Parallel benefit",
            text: "The digest explicitly links recurrence removal to increased parallel computation.",
            confidence: 0.88,
          },
        ],
        D: [
          {
            short_label: "Order preservation",
            text: "Sequence order must still be represented, so positional encodings act as a compensating governance layer over token positions.",
            source_kind: "explicit",
            status: "explicit",
            confidence: 0.83,
            warrant: "Order preservation is stated directly in the digest.",
          },
        ],
        U: [
          {
            short_label: "Efficiency",
            text: "The utility target is reduced training cost and faster throughput without surrendering sequence competence.",
            confidence: 0.86,
          },
        ],
      },
    },
    {
      key: "c3",
      anchor: "delivers stronger quality with lower training cost",
      claim_text: "The Transformer delivers stronger translation quality with lower training cost on benchmarks.",
      summary: "Empirical claim: benchmark performance supports the architecture change.",
      confidence: 0.88,
      lanes: {
        O: [
          {
            short_label: "Benchmark object",
            text: "Machine translation tasks and quality metrics are the operative evaluation objects.",
            confidence: 0.84,
          },
        ],
        E: [
          {
            short_label: "Benchmark support",
            text: "The digest says the model delivers stronger quality with lower cost on machine translation benchmarks.",
            confidence: 0.9,
          },
        ],
        U: [
          {
            short_label: "General mechanism claim",
            text: "The benchmark result is used to justify the broader utility claim that attention can be the primary sequence modeling mechanism.",
            confidence: 0.78,
          },
        ],
      },
      diagnostics: [
        {
          kind: "u_overreach",
          severity: "warning",
          summary: "A translation benchmark is used to support a wider mechanism claim about sequence modeling in general.",
          lane_ids: ["E", "U"],
        },
      ],
    },
  ],
  "bert-pre-training": [
    {
      key: "c1",
      anchor: "pre-trains deep bidirectional representations",
      claim_text: "BERT pre-trains deep bidirectional representations by masking tokens and using sentence-level relation prediction.",
      summary: "Representation claim: bidirectional pre-training is the main ontological shift.",
      confidence: 0.93,
      lanes: {
        O: [
          {
            short_label: "Bidirectional rep",
            text: "Language understanding is modeled through deep bidirectional token representations rather than one-way context accumulation.",
            confidence: 0.94,
          },
        ],
        E: [
          {
            short_label: "Mask objective",
            text: "Masked token prediction and sentence-level relation prediction are presented as the explicit pre-training evidence surfaces.",
            confidence: 0.89,
          },
        ],
        D: [
          {
            short_label: "Corruption rule",
            text: "The training regime requires partially masking source tokens so the model cannot trivially copy its inputs.",
            source_kind: "inferred",
            status: "inferred",
            confidence: 0.72,
          },
        ],
        U: [
          {
            short_label: "Reusable language prior",
            text: "The utility target is a reusable language representation that transfers across many downstream tasks.",
            confidence: 0.84,
          },
        ],
      },
      diagnostics: [
        {
          kind: "implicit_assumption",
          severity: "advisory",
          summary: "The digest leaves the exact corruption discipline implicit even though it is crucial to the epistemic path.",
          lane_ids: ["D", "E"],
        },
      ],
    },
    {
      key: "c2",
      anchor: "fine-tuned with minimal task-specific changes",
      claim_text: "The resulting model can be fine-tuned with minimal task-specific changes.",
      summary: "Adaptation claim: pre-training reduces downstream bespoke modeling effort.",
      confidence: 0.87,
      lanes: {
        O: [
          {
            short_label: "Shared base model",
            text: "A single pre-trained base representation is reused across many task heads.",
            confidence: 0.83,
          },
        ],
        E: [
          {
            short_label: "Transfer behavior",
            text: "The source explicitly says fine-tuning requires minimal task-specific changes.",
            confidence: 0.86,
          },
        ],
        D: [
          {
            short_label: "Task head restraint",
            text: "Downstream adaptation is normatively constrained to be light-touch rather than a ground-up redesign.",
            source_kind: "inferred",
            status: "inferred",
            confidence: 0.69,
          },
        ],
        U: [
          {
            short_label: "Engineering leverage",
            text: "The payoff is faster adaptation and a lower per-task engineering burden.",
            confidence: 0.81,
          },
        ],
      },
    },
    {
      key: "c3",
      anchor: "strong benchmark results",
      claim_text: "BERT produces strong benchmark results across several NLP tasks.",
      summary: "Evidence claim: benchmark breadth is used to support general transfer usefulness.",
      confidence: 0.85,
      lanes: {
        O: [
          {
            short_label: "Benchmark set",
            text: "Question answering, natural language inference, and token-level prediction tasks form the evaluated task family.",
            confidence: 0.82,
          },
        ],
        E: [
          {
            short_label: "Task breadth",
            text: "The digest explicitly reports strong results across multiple benchmark families.",
            confidence: 0.88,
          },
        ],
        U: [
          {
            short_label: "Broad usefulness",
            text: "The paper projects these results into the broader claim that bidirectional pre-training is generally useful.",
            confidence: 0.74,
          },
        ],
      },
      diagnostics: [
        {
          kind: "u_overreach",
          severity: "advisory",
          summary: "Benchmark breadth supports transfer usefulness, but the generalization horizon remains broader than the evidence surface itself.",
          lane_ids: ["E", "U"],
        },
      ],
    },
  ],
  "gpt3-few-shot": [
    {
      key: "c1",
      anchor: "175-billion-parameter model",
      claim_text: "GPT-3 scales autoregressive language modeling to 175 billion parameters.",
      summary: "Scaling claim: increasing model size changes capability shape.",
      confidence: 0.92,
      lanes: {
        O: [
          {
            short_label: "Large autoregressive LM",
            text: "The operative object is a very large autoregressive language model whose capacity is treated as a first-order variable.",
            confidence: 0.93,
          },
        ],
        E: [
          {
            short_label: "Scale observation",
            text: "The digest explicitly names a 175-billion-parameter model as the central experimental object.",
            confidence: 0.9,
          },
        ],
        U: [
          {
            short_label: "Capability from scale",
            text: "The utility target is greater task competence obtained through scaling rather than task-specific gradient updates.",
            confidence: 0.82,
          },
        ],
      },
    },
    {
      key: "c2",
      anchor: "many tasks can be steered by prompts",
      claim_text: "Many tasks can be steered by prompts and a few examples without gradient updates.",
      summary: "Interaction claim: prompt conditioning becomes the main interface for adaptation.",
      confidence: 0.9,
      lanes: {
        O: [
          {
            short_label: "Prompt-conditioned behavior",
            text: "Task adaptation is re-specified as prompt conditioning over a single base model rather than parameter updates per task.",
            confidence: 0.91,
          },
        ],
        E: [
          {
            short_label: "Few-shot observation",
            text: "The digest explicitly states that many tasks can be steered by prompts and small example sets.",
            confidence: 0.88,
          },
        ],
        D: [
          {
            short_label: "No weight update path",
            text: "The adaptation pathway is constrained to context construction instead of additional training steps.",
            source_kind: "explicit",
            status: "explicit",
            confidence: 0.8,
            warrant: "The no-gradient-update point is explicit in the digest.",
          },
        ],
        U: [
          {
            short_label: "General interface",
            text: "The payoff is a more general-purpose text interface for task specification.",
            confidence: 0.79,
          },
        ],
      },
      subclaims: [
        {
          key: "c2a",
          anchor: "without gradient updates",
          claim_text: "The adaptation pathway excludes task-specific gradient updates.",
          summary: "Subclaim: inference-time conditioning becomes the dominant fast path.",
          confidence: 0.84,
          lanes: {
            D: [
              {
                short_label: "Context-only adaptation",
                text: "Task steering is normatively bounded to prompt and example construction during use time.",
                confidence: 0.83,
              },
            ],
            U: [
              {
                short_label: "Fast adaptation",
                text: "This shortens the path from user intent to system response by avoiding re-training loops.",
                source_kind: "inferred",
                status: "inferred",
                confidence: 0.66,
              },
            ],
          },
        },
      ],
    },
    {
      key: "c3",
      anchor: "performance is often competitive but still uneven",
      claim_text: "Performance is often competitive but still uneven, with limits around reasoning consistency, calibration, and bias.",
      summary: "Qualification claim: the capability claim is explicitly bounded by observed failure modes.",
      confidence: 0.89,
      lanes: {
        E: [
          {
            short_label: "Uneven evidence",
            text: "The digest itself qualifies performance as competitive in some settings but uneven overall.",
            confidence: 0.9,
          },
        ],
        D: [
          {
            short_label: "Caution boundary",
            text: "Deployment claims should remain bounded by stated reliability and bias limits.",
            source_kind: "inferred",
            status: "inferred",
            confidence: 0.73,
          },
        ],
        U: [
          {
            short_label: "Broad capability narrative",
            text: "The surrounding scaling narrative still projects the system as a broadly capable few-shot learner.",
            confidence: 0.78,
          },
        ],
      },
      diagnostics: [
        {
          kind: "underdetermination",
          severity: "warning",
          summary: "Capability breadth is reported with explicit caveats, leaving the true generality envelope partially open.",
          lane_ids: ["E", "U"],
        },
      ],
    },
  ],
  "clip-natural-language-supervision": [
    {
      key: "c1",
      anchor: "produce transferable representations",
      claim_text: "Training on internet-scale image and text pairs can produce transferable representations.",
      summary: "Representation claim: natural language supervision substitutes for closed label taxonomies.",
      confidence: 0.91,
      lanes: {
        O: [
          {
            short_label: "Shared embedding",
            text: "Images and text are treated as co-typed objects that can inhabit a shared representational space.",
            confidence: 0.91,
          },
        ],
        E: [
          {
            short_label: "Internet-scale pairing",
            text: "The digest explicitly grounds the approach in internet-scale image-text pair supervision.",
            confidence: 0.88,
          },
        ],
        U: [
          {
            short_label: "Transfer",
            text: "The objective is a representation that transfers without task-specific supervised relabeling.",
            confidence: 0.86,
          },
        ],
      },
    },
    {
      key: "c2",
      anchor: "allowing downstream recognition tasks to be expressed as text matching",
      claim_text: "Recognition tasks can be expressed as text matching in the shared embedding space.",
      summary: "Interface claim: language becomes the task specification surface for recognition.",
      confidence: 0.9,
      lanes: {
        O: [
          {
            short_label: "Language-conditioned retrieval",
            text: "Recognition is re-framed as retrieval and comparison inside a joint image-language space.",
            confidence: 0.9,
          },
        ],
        E: [
          {
            short_label: "Task expression",
            text: "The digest explicitly says downstream recognition can be expressed as text matching.",
            confidence: 0.89,
          },
        ],
        D: [
          {
            short_label: "Prompt typing",
            text: "Task labels now need to be phrased as text prompts or textual descriptors to become actionable queries.",
            source_kind: "inferred",
            status: "inferred",
            confidence: 0.75,
          },
        ],
        U: [
          {
            short_label: "Zero-shot path",
            text: "The payoff is zero-shot transfer without retraining a closed classifier for every target dataset.",
            confidence: 0.87,
          },
        ],
      },
    },
    {
      key: "c3",
      anchor: "reduces dependence on bespoke supervised label sets",
      claim_text: "The system reduces dependence on bespoke supervised label sets.",
      summary: "Governance claim: fixed label taxonomies lose authority as the only recognition interface.",
      confidence: 0.83,
      lanes: {
        O: [
          {
            short_label: "Label taxonomy displaced",
            text: "Closed taxonomies are no longer the only ontology allowed for recognition tasks.",
            confidence: 0.82,
          },
        ],
        D: [
          {
            short_label: "Prompt care",
            text: "The burden shifts toward careful prompt wording and template design, which remain only partially specified in the digest.",
            source_kind: "inferred",
            status: "underdetermined",
            confidence: 0.52,
          },
        ],
        U: [
          {
            short_label: "Less bespoke supervision",
            text: "The utility claim is lower task-specific dataset engineering and broader transfer reach.",
            confidence: 0.81,
          },
        ],
      },
      diagnostics: [
        {
          kind: "underdetermination",
          severity: "advisory",
          summary: "The new prompt-mediated control surface is useful but only lightly specified in the abstract-level artifact.",
          lane_ids: ["D"],
        },
      ],
    },
  ],
  "alphago-search-and-neural-networks": [
    {
      key: "c1",
      anchor: "coupled with Monte Carlo tree search",
      claim_text: "Deep neural networks can be coupled with Monte Carlo tree search to choose strong moves in Go.",
      summary: "Coupling claim: learned evaluation and explicit search are jointly necessary.",
      confidence: 0.93,
      lanes: {
        O: [
          {
            short_label: "Hybrid planner",
            text: "The operative system is a hybrid object composed of learned networks plus explicit search.",
            confidence: 0.94,
          },
        ],
        E: [
          {
            short_label: "Coupling statement",
            text: "The digest directly states that neural networks are coupled with Monte Carlo tree search.",
            confidence: 0.9,
          },
        ],
        D: [
          {
            short_label: "Tight coordination",
            text: "Search and learned evaluation must be tightly coordinated rather than treated as independent modules.",
            source_kind: "inferred",
            status: "inferred",
            confidence: 0.77,
          },
        ],
        U: [
          {
            short_label: "Strong move choice",
            text: "The utility target is stronger decision quality in a difficult planning domain.",
            confidence: 0.87,
          },
        ],
      },
    },
    {
      key: "c2",
      anchor: "Policy networks narrow attention to promising actions",
      claim_text: "Policy networks narrow attention to promising actions and value networks estimate position strength.",
      summary: "Functional decomposition claim: policy and value play distinct roles in the decision stack.",
      confidence: 0.9,
      lanes: {
        O: [
          {
            short_label: "Policy/value roles",
            text: "The system ontology distinguishes action-selection guidance from position-evaluation guidance.",
            confidence: 0.9,
          },
        ],
        E: [
          {
            short_label: "Role split",
            text: "The digest explicitly assigns one network to action narrowing and another to position strength estimation.",
            confidence: 0.89,
          },
        ],
        U: [
          {
            short_label: "Search efficiency",
            text: "The combined roles aim to focus computation on useful branches and avoid exhaustive exploration.",
            confidence: 0.82,
          },
        ],
      },
    },
    {
      key: "c3",
      anchor: "defeats a professional human player",
      claim_text: "AlphaGo defeats a professional human player, supporting the claim that learned evaluation and search can be effectively combined.",
      summary: "Empirical claim: a concrete milestone is used to validate the hybrid architecture.",
      confidence: 0.88,
      lanes: {
        E: [
          {
            short_label: "Human match result",
            text: "The digest uses a professional-player victory as the central empirical validation event.",
            confidence: 0.91,
          },
        ],
        U: [
          {
            short_label: "Hybrid validation",
            text: "The system projects that milestone into a broader claim about governed coupling between learning and search.",
            confidence: 0.8,
          },
        ],
      },
      diagnostics: [
        {
          kind: "u_overreach",
          severity: "advisory",
          summary: "One milestone event validates the hybrid in Go, but not every planning domain with equal strength.",
          lane_ids: ["E", "U"],
        },
      ],
    },
  ],
};

type SentenceRecord = {
  text: string;
  start: number;
  end: number;
  index: number;
};

function slugify(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "")
    .slice(0, 48);
}

function sentenceRecords(text: string): SentenceRecord[] {
  const records: SentenceRecord[] = [];
  const regex = /[^.!?]+[.!?]?/g;
  let match: RegExpExecArray | null;
  let index = 0;
  while ((match = regex.exec(text)) !== null) {
    const raw = match[0];
    const trimmed = raw.trim();
    if (!trimmed) continue;
    const startOffset = raw.indexOf(trimmed);
    const start = match.index + Math.max(0, startOffset);
    const end = start + trimmed.length;
    records.push({ text: trimmed, start, end, index });
    index += 1;
  }
  return records;
}

function findSpan(text: string, anchor: string): { start: number; end: number } | null {
  const normalizedText = text.toLowerCase();
  const normalizedAnchor = anchor.toLowerCase();
  const start = normalizedText.indexOf(normalizedAnchor);
  if (start === -1) return null;
  return { start, end: start + anchor.length };
}

function resolveSentenceIndex(records: SentenceRecord[], start: number, end: number): number {
  const match = records.find((record) => start >= record.start && end <= record.end);
  return match?.index ?? 0;
}

function placeholderLaneFragment(lane: LaneId): CuratedLaneSpec {
  if (lane === "O") {
    return {
      short_label: "No isolated object",
      text: "The claim does not isolate a distinct ontology beyond the source sentence itself.",
      source_kind: "inferred",
      status: "missing",
      confidence: PLACEHOLDER_CONFIDENCE,
      warrant: "Generated placeholder because no explicit ontology fragment was supplied.",
    };
  }
  if (lane === "E") {
    return {
      short_label: "Support not explicit",
      text: "The supporting evidence surface is not explicit enough to isolate beyond the selected claim span.",
      source_kind: "inferred",
      status: "missing",
      confidence: PLACEHOLDER_CONFIDENCE,
      warrant: "Generated placeholder because no explicit evidence fragment was supplied.",
    };
  }
  if (lane === "D") {
    return {
      short_label: "Constraint implicit",
      text: "The governing constraint or normative envelope remains implicit in the source claim.",
      source_kind: "inferred",
      status: "missing",
      confidence: PLACEHOLDER_CONFIDENCE,
      warrant: "Generated placeholder because no deontic fragment was supplied.",
    };
  }
  return {
    short_label: "Objective implicit",
    text: "The utility target is implicit or absent at the selected claim span.",
    source_kind: "inferred",
    status: "missing",
    confidence: PLACEHOLDER_CONFIDENCE,
    warrant: "Generated placeholder because no utility fragment was supplied.",
  };
}

function normalizeLaneFragment(spec: CuratedLaneSpec): Required<CuratedLaneSpec> {
  return {
    short_label: spec.short_label,
    text: spec.text,
    source_kind: spec.source_kind ?? "explicit",
    status: spec.status ?? (spec.source_kind === "inferred" ? "inferred" : "explicit"),
    confidence: clampConfidence(spec.confidence ?? 0.78),
    warrant: spec.warrant ?? "Derived from the selected claim surface.",
  };
}

function bridgeKindForFragments(from: ODEULaneFragment, to: ODEULaneFragment): BridgeKind {
  if (from.status === "missing" || to.status === "missing") return "missing_bridge";
  if (from.status === "contested" || to.status === "contested") return "contested_bridge";
  if (from.status === "underdetermined" || to.status === "underdetermined") {
    return "missing_bridge";
  }
  if (from.source_kind === "inferred" || to.source_kind === "inferred") {
    return "projection_bridge";
  }
  return "canonical_bridge";
}

function defaultBridgeRationale(from: ODEULaneFragment, to: ODEULaneFragment): string {
  if (to.status === "missing") {
    return `The ${to.lane} lane is not explicit enough to close the bridge from ${from.lane}.`;
  }
  if (to.status === "underdetermined") {
    return `The ${to.lane} lane is only partially specified, so the ${from.lane}→${to.lane} bridge remains weak.`;
  }
  if (to.source_kind === "inferred") {
    return `The ${from.lane} fragment supports an inferred ${to.lane} projection rather than a source-authored one.`;
  }
  return `The ${from.lane} fragment canonically supports the ${to.lane} fragment for this claim.`;
}

function containsAny(text: string, terms: string[]): boolean {
  const normalized = text.toLowerCase();
  return terms.some((term) => normalized.includes(term));
}

function inferStatusFromConfidence(confidence: number): FragmentStatus {
  if (confidence >= 0.8) return "explicit";
  if (confidence >= 0.58) return "inferred";
  return "underdetermined";
}

function heuristicOntologyText(sentence: string): string {
  const cleaned = sentence.replace(/[.,;:]/g, "").trim();
  const tokens = cleaned.split(/\s+/).filter(Boolean);
  const keep = tokens.filter((token) => !STOP_WORDS.has(token.toLowerCase())).slice(0, 9);
  const head = keep.join(" ");
  return head
    ? `Primary modeled entities: ${head}.`
    : "Primary modeled entities remain broad and only weakly isolated in the source sentence.";
}

function heuristicUtilityText(sentence: string): string {
  const normalized = sentence.toLowerCase();
  if (containsAny(normalized, ["improve", "better", "strong", "competitive", "transfer"])) {
    return "The utility target is improved task performance or transfer quality.";
  }
  if (containsAny(normalized, ["reduce", "lower", "faster", "parallel", "efficient"])) {
    return "The utility target is improved efficiency, speed, or lower training cost.";
  }
  if (containsAny(normalized, ["enable", "allow", "steer", "express"])) {
    return "The utility target is a more general interface for getting desired behavior from the system.";
  }
  return "The utility target is only implicit and must be reconstructed from surrounding context.";
}

function heuristicDeonticText(sentence: string): string {
  const normalized = sentence.toLowerCase();
  if (containsAny(normalized, ["without", "must", "requires", "bounded", "only", "while"])) {
    return "The claim implies a constraint envelope that must hold for the mechanism to remain valid.";
  }
  if (containsAny(normalized, ["prompt", "fine-tune", "mask", "encoding", "search"])) {
    return "The method depends on a specific procedural discipline even if the abstract does not spell it out fully.";
  }
  return "Constraint structure is mostly implicit at this level of the source artifact.";
}

function heuristicEvidenceText(sentence: string): { text: string; confidence: number; status: FragmentStatus } {
  const normalized = sentence.toLowerCase();
  if (/\d/.test(sentence) || containsAny(normalized, ["benchmark", "results", "shows", "achieves", "defeats", "performance"])) {
    return {
      text: `The source sentence itself is being used as the immediate evidence surface: ${sentence}`,
      confidence: 0.71,
      status: /\d/.test(sentence) ? "explicit" : "underdetermined",
    };
  }
  return {
    text: "The source sentence states a claim, but benchmark or quantitative support is not explicit within the selected span.",
    confidence: 0.45,
    status: "underdetermined",
  };
}

function sentenceToHeuristicClaimSpec(sentence: string, index: number, depth: WorkbenchDepth): CuratedClaimSpec {
  const evidence = heuristicEvidenceText(sentence);
  const utilityText = heuristicUtilityText(sentence);
  const deonticText = heuristicDeonticText(sentence);
  const utilityConfidence = utilityText.includes("implicit") ? 0.42 : 0.62;
  const deonticConfidence = deonticText.includes("implicit") ? 0.38 : 0.58;
  const diagnostics: CuratedDiagnosticSpec[] = [];

  if (evidence.status === "underdetermined") {
    diagnostics.push({
      kind: "underdetermination",
      severity: "warning",
      summary: "The selected claim lacks a strong local evidence surface inside the sentence itself.",
      lane_ids: ["E"],
    });
  }
  if (utilityConfidence > evidence.confidence + 0.1) {
    diagnostics.push({
      kind: "u_overreach",
      severity: "warning",
      summary: "The utility projection is stronger than the evidence surface directly visible in the source sentence.",
      lane_ids: ["E", "U"],
    });
  }
  if (deonticConfidence < 0.5) {
    diagnostics.push({
      kind: "implicit_assumption",
      severity: "advisory",
      summary: "Constraint structure is mostly inferred rather than source-authored at abstract level.",
      lane_ids: ["D"],
    });
  }
  if (containsAny(sentence, ["reasoning", "general", "understanding", "alignment", "semantic", "knowledge"])) {
    diagnostics.push({
      kind: "overloaded_term",
      severity: "advisory",
      summary: "The sentence uses a semantically loaded term whose operational meaning remains broad.",
      lane_ids: ["O", "U"],
    });
  }

  const subclaims = depth === 2 ? clauseSubclaims(sentence, index) : undefined;

  return {
    key: `h${index + 1}`,
    anchor: sentence.slice(0, Math.min(sentence.length, 72)),
    claim_text: sentence,
    summary: `Heuristic decomposition for sentence ${index + 1}.`,
    confidence: 0.62,
    lanes: {
      O: [
        {
          short_label: "Claim object",
          text: heuristicOntologyText(sentence),
          confidence: 0.61,
          status: inferStatusFromConfidence(0.61),
        },
      ],
      E: [
        {
          short_label: "Local evidence",
          text: evidence.text,
          confidence: evidence.confidence,
          status: evidence.status,
        },
      ],
      D: [
        {
          short_label: "Constraint envelope",
          text: deonticText,
          source_kind: "inferred",
          confidence: deonticConfidence,
          status: inferStatusFromConfidence(deonticConfidence),
        },
      ],
      U: [
        {
          short_label: "Utility projection",
          text: utilityText,
          source_kind: utilityConfidence < 0.55 ? "inferred" : "explicit",
          confidence: utilityConfidence,
          status: inferStatusFromConfidence(utilityConfidence),
        },
      ],
    },
    diagnostics,
    subclaims,
  };
}

function clauseSubclaims(sentence: string, index: number): CuratedClaimSpec[] {
  const parts = sentence
    .split(/,|;|\band\b/gi)
    .map((part) => part.trim())
    .filter((part) => part.length > 18)
    .slice(0, 3);
  if (parts.length <= 1) return [];
  return parts.map((part, partIndex) => ({
    key: `h${index + 1}-s${partIndex + 1}`,
    anchor: part.slice(0, Math.min(part.length, 48)),
    claim_text: part,
    summary: `Clause-level subclaim ${partIndex + 1}.`,
    confidence: 0.56,
    lanes: {
      O: [
        {
          short_label: "Clause object",
          text: heuristicOntologyText(part),
          confidence: 0.56,
          status: inferStatusFromConfidence(0.56),
        },
      ],
      E: [
        {
          short_label: "Clause evidence",
          text: `The clause is directly sourced from the parent sentence: ${part}`,
          confidence: 0.55,
          status: "explicit",
        },
      ],
      D: [
        {
          short_label: "Clause constraint",
          text: heuristicDeonticText(part),
          source_kind: "inferred",
          confidence: 0.42,
          status: "underdetermined",
        },
      ],
      U: [
        {
          short_label: "Clause utility",
          text: heuristicUtilityText(part),
          source_kind: "inferred",
          confidence: 0.48,
          status: "underdetermined",
        },
      ],
    },
    diagnostics: [
      {
        kind: "implicit_assumption",
        severity: "advisory",
        summary: "Clause-level D/U interpretation is mostly reconstructed by inference.",
        lane_ids: ["D", "U"],
      },
    ],
  }));
}

const STOP_WORDS = new Set([
  "a",
  "an",
  "and",
  "are",
  "as",
  "at",
  "be",
  "by",
  "for",
  "from",
  "in",
  "is",
  "it",
  "of",
  "on",
  "or",
  "that",
  "the",
  "their",
  "this",
  "to",
  "with",
  "while",
]);

function buildArtifactFromClaimSpecs({
  source,
  claimSpecs,
  depth,
  pipelineMode,
  processorVersion,
}: {
  source: PaperSemanticSource;
  claimSpecs: CuratedClaimSpec[];
  depth: WorkbenchDepth;
  pipelineMode: ProcessingPipelineMode;
  processorVersion: string;
}): PaperSemanticWorkbenchArtifact {
  const sentences = sentenceRecords(source.source_text);
  const spans: PaperClaimSpan[] = [];
  const claims: ODEUClaimDecomposition[] = [];
  const fragments: ODEULaneFragment[] = [];
  const bridges: ODEUInferenceBridge[] = [];
  const diagnostics: ODEUSemanticDiagnostic[] = [];
  const laneNodeOrder: Record<LaneId, string[]> = { O: [], E: [], D: [], U: [] };
  const inlineClaimOrder: string[] = [];

  const buildClaim = (spec: CuratedClaimSpec, parentClaimId: string | null): string => {
    const claimId = `${source.source_id}::claim::${slugify(parentClaimId ? `${parentClaimId}-${spec.key}` : spec.key)}`;
    const spanRef = findSpan(source.source_text, spec.anchor) ?? findSpan(source.source_text, spec.claim_text) ?? { start: 0, end: Math.min(source.source_text.length, Math.max(20, spec.anchor.length || spec.claim_text.length)) };
    const spanId = `${claimId}::span::0`;
    const span = {
      schema: "paper_claim_span@1",
      span_id: spanId,
      start: spanRef.start,
      end: spanRef.end,
      quote: source.source_text.slice(spanRef.start, spanRef.end),
      sentence_index: resolveSentenceIndex(sentences, spanRef.start, spanRef.end),
      paragraph_index: 0,
    } satisfies PaperClaimSpan;
    spans.push(span);

    const fragmentIds: string[] = [];
    const fragmentByLane: Partial<Record<LaneId, ODEULaneFragment>> = {};

    LANE_ORDER.forEach((lane) => {
      const laneSpecs = spec.lanes[lane] && spec.lanes[lane]!.length > 0 ? spec.lanes[lane]! : [placeholderLaneFragment(lane)];
      laneSpecs.forEach((laneSpec, laneIndex) => {
        const normalized = normalizeLaneFragment(laneSpec);
        const fragmentId = `${claimId}::${lane.toLowerCase()}::${laneIndex}`;
        const fragment: ODEULaneFragment = {
          schema: "odeu_lane_fragment@1",
          fragment_id: fragmentId,
          claim_id: claimId,
          lane,
          short_label: normalized.short_label,
          text: normalized.text,
          source_kind: normalized.source_kind,
          status: normalized.status,
          confidence: normalized.confidence,
          warrant: normalized.warrant,
          span_ids: [spanId],
          bridge_ids: [],
          diagnostic_ids: [],
        };
        fragments.push(fragment);
        fragmentIds.push(fragmentId);
        laneNodeOrder[lane].push(fragmentId);
        if (!fragmentByLane[lane]) {
          fragmentByLane[lane] = fragment;
        }
      });
    });

    const childIds = depth === 2 ? (spec.subclaims ?? []).map((childSpec) => buildClaim(childSpec, claimId)) : [];

    const claimDiagnostics: ODEUSemanticDiagnostic[] = [];
    (spec.diagnostics ?? []).forEach((diagSpec, diagIndex) => {
      const relatedFragments = (diagSpec.lane_ids ?? [])
        .map((lane) => fragmentByLane[lane]?.fragment_id)
        .filter((value): value is string => Boolean(value));
      const diagnostic: ODEUSemanticDiagnostic = {
        schema: "odeu_semantic_diagnostics@1",
        diagnostic_id: `${claimId}::diag::manual-${diagIndex}`,
        claim_id: claimId,
        kind: diagSpec.kind,
        severity: diagSpec.severity,
        summary: diagSpec.summary,
        lane_ids: diagSpec.lane_ids ?? [],
        related_fragment_ids: relatedFragments,
        span_ids: [spanId],
      };
      claimDiagnostics.push(diagnostic);
    });

    const bridgePairs: Array<[LaneId, LaneId]> = [
      ["O", "E"],
      ["O", "D"],
      ["E", "U"],
      ["D", "U"],
    ];
    bridgePairs.forEach(([fromLane, toLane], pairIndex) => {
      const fromFragment = fragmentByLane[fromLane];
      const toFragment = fragmentByLane[toLane];
      if (!fromFragment || !toFragment) return;
      const diagnosticIds: string[] = [];

      if (toFragment.status === "missing" || fromFragment.status === "missing") {
        const diagnostic: ODEUSemanticDiagnostic = {
          schema: "odeu_semantic_diagnostics@1",
          diagnostic_id: `${claimId}::diag::bridge-missing-${pairIndex}`,
          claim_id: claimId,
          kind: "missing_bridge",
          severity: "warning",
          summary: `The ${fromLane}→${toLane} bridge is incomplete because one lane remains missing or only weakly typed.`,
          lane_ids: [fromLane, toLane],
          related_fragment_ids: [fromFragment.fragment_id, toFragment.fragment_id],
          span_ids: [spanId],
        };
        claimDiagnostics.push(diagnostic);
        diagnosticIds.push(diagnostic.diagnostic_id);
      }

      if (
        toLane === "U" &&
        fromLane === "E" &&
        toFragment.confidence > fromFragment.confidence + 0.12
      ) {
        const diagnostic: ODEUSemanticDiagnostic = {
          schema: "odeu_semantic_diagnostics@1",
          diagnostic_id: `${claimId}::diag::u-overreach-${pairIndex}`,
          claim_id: claimId,
          kind: "u_overreach",
          severity: "warning",
          summary: "Utility projection is stronger than the directly visible evidence support inside this claim.",
          lane_ids: [fromLane, toLane],
          related_fragment_ids: [fromFragment.fragment_id, toFragment.fragment_id],
          span_ids: [spanId],
        };
        claimDiagnostics.push(diagnostic);
        diagnosticIds.push(diagnostic.diagnostic_id);
      }

      const bridge: ODEUInferenceBridge = {
        schema: "odeu_inference_bridge@1",
        bridge_id: `${claimId}::bridge::${fromLane.toLowerCase()}-${toLane.toLowerCase()}`,
        claim_id: claimId,
        from_fragment_id: fromFragment.fragment_id,
        to_fragment_id: toFragment.fragment_id,
        kind: bridgeKindForFragments(fromFragment, toFragment),
        rationale: defaultBridgeRationale(fromFragment, toFragment),
        confidence: clampConfidence((fromFragment.confidence + toFragment.confidence) / 2),
        diagnostic_ids: diagnosticIds,
      };
      bridges.push(bridge);
      fromFragment.bridge_ids.push(bridge.bridge_id);
      toFragment.bridge_ids.push(bridge.bridge_id);
    });

    claimDiagnostics.forEach((diagnostic) => {
      diagnostics.push(diagnostic);
      diagnostic.related_fragment_ids.forEach((fragmentId) => {
        const fragment = fragments.find((item) => item.fragment_id === fragmentId);
        if (fragment && !fragment.diagnostic_ids.includes(diagnostic.diagnostic_id)) {
          fragment.diagnostic_ids.push(diagnostic.diagnostic_id);
        }
      });
    });

    claims.push({
      schema: "odeu_claim_decomposition@1",
      claim_id: claimId,
      parent_claim_id: parentClaimId,
      depth: parentClaimId ? 2 : 1,
      claim_text: spec.claim_text,
      summary: spec.summary,
      span_ids: [spanId],
      explicitness: spec.explicitness ?? "explicit",
      confidence: clampConfidence(spec.confidence ?? 0.78),
      status: spec.status ?? "stable",
      lane_fragment_ids: fragmentIds,
      subclaim_ids: childIds,
      diagnostic_ids: claimDiagnostics.map((diagnostic) => diagnostic.diagnostic_id),
    });

    if (!parentClaimId) {
      inlineClaimOrder.push(claimId);
    }

    return claimId;
  };

  claimSpecs.forEach((spec) => {
    buildClaim(spec, null);
  });

  const visualProjection: ODEUVisualProjection = {
    schema: "odeu_visual_projection@1",
    default_view: "artifact",
    lane_order: [...LANE_ORDER],
    inline_claim_order: inlineClaimOrder,
    recommended_focus_claim_id: inlineClaimOrder[0] ?? null,
    lane_node_order: laneNodeOrder,
  };

  return {
    schema: "paper_semantic_workbench@1",
    artifact_id: `${source.source_id}::${pipelineMode}::d${depth}`,
    source,
    processing: {
      pipeline_mode: pipelineMode,
      processor_version: processorVersion,
      depth_requested: depth,
      generated_at: new Date().toISOString(),
      authority_posture: {
        source_artifact_authority: "reference-anchor",
        semantic_projection_authority: "advisory-only",
        inferred_content_authority: "non-authoritative",
      },
      worker:
        pipelineMode === "resident-codex"
          ? {
              template_id: "adeu.paper.semantic_decomposition.v0",
              template_version: "v0",
              status: "idle",
            }
          : undefined,
    },
    spans,
    claims: sortClaims(claims),
    lane_fragments: fragments,
    inference_bridges: bridges,
    diagnostics,
    visual_projection: visualProjection,
  };
}

function sortClaims(claims: ODEUClaimDecomposition[]): ODEUClaimDecomposition[] {
  return [...claims].sort((left, right) => {
    if (left.depth !== right.depth) return left.depth - right.depth;
    return left.claim_id.localeCompare(right.claim_id);
  });
}

function paperToSource(paper: SamplePaper): PaperSemanticSource {
  return {
    schema: "paper_claim_source@1",
    source_id: paper.paper_id,
    artifact_kind: paper.artifact_kind,
    title: paper.title,
    authors: paper.authors,
    year: paper.year,
    venue: paper.venue,
    source_text: paper.source_text,
    source_notes: paper.source_notes,
  };
}

function heuristicSpecsFromText(text: string, depth: WorkbenchDepth): CuratedClaimSpec[] {
  const sentences = sentenceRecords(text)
    .map((record) => record.text)
    .filter((sentence) => sentence.length > 24)
    .slice(0, 5);
  const fallback =
    sentences.length > 0
      ? sentences
      : [text.trim().slice(0, Math.min(text.trim().length, 240)) || "No source sentence available."];
  return fallback.map((sentence, index) => sentenceToHeuristicClaimSpec(sentence, index, depth));
}

export function getSamplePaper(paperId: string): SamplePaper | undefined {
  return SAMPLE_PAPERS.find((paper) => paper.paper_id === paperId);
}

export function buildCuratedPaperArtifact(
  paperId: string,
  depth: WorkbenchDepth,
): PaperSemanticWorkbenchArtifact | null {
  const paper = getSamplePaper(paperId);
  const claimSpecs = paper ? CURATED_SPECS[paper.paper_id] : null;
  if (!paper || !claimSpecs) return null;
  return buildArtifactFromClaimSpecs({
    source: paperToSource(paper),
    claimSpecs,
    depth,
    pipelineMode: "mock-curated",
    processorVersion: DEFAULT_PROCESSOR_VERSION,
  });
}

export function buildHeuristicPaperArtifact({
  title,
  sourceText,
  depth,
}: {
  title?: string;
  sourceText: string;
  depth: WorkbenchDepth;
}): PaperSemanticWorkbenchArtifact {
  const source: PaperSemanticSource = {
    schema: "paper_claim_source@1",
    source_id: `pasted-${slugify(title || sourceText.slice(0, 36) || "artifact")}`,
    artifact_kind: "pasted.paragraph",
    title: title?.trim() || "Pasted abstract",
    authors: [],
    year: null,
    source_text: sourceText.trim(),
    source_notes: [
      "This artifact was decomposed by the heuristic mock path.",
      "Use resident Codex mode for future live runtime decomposition through the ADEU harness.",
    ],
  };

  return buildArtifactFromClaimSpecs({
    source,
    claimSpecs: heuristicSpecsFromText(source.source_text, depth),
    depth,
    pipelineMode: "mock-heuristic",
    processorVersion: HEURISTIC_PROCESSOR_VERSION,
  });
}

export function runMockSemanticProcessing({
  samplePaperId,
  pastedText,
  title,
  depth,
}: {
  samplePaperId: string | null;
  pastedText: string;
  title?: string;
  depth: WorkbenchDepth;
}): PaperSemanticWorkbenchArtifact {
  const trimmed = pastedText.trim();
  if (trimmed) {
    return buildHeuristicPaperArtifact({ title, sourceText: trimmed, depth });
  }
  if (samplePaperId) {
    const artifact = buildCuratedPaperArtifact(samplePaperId, depth);
    if (artifact) return artifact;
  }
  const fallbackPaper = SAMPLE_PAPERS[0];
  return buildArtifactFromClaimSpecs({
    source: paperToSource(fallbackPaper),
    claimSpecs: CURATED_SPECS[fallbackPaper.paper_id],
    depth,
    pipelineMode: "mock-curated",
    processorVersion: DEFAULT_PROCESSOR_VERSION,
  });
}

export function summarizeProcessingSource(artifact: PaperSemanticWorkbenchArtifact): string {
  if (artifact.processing.pipeline_mode === "mock-curated") {
    return "curated sample artifact";
  }
  if (artifact.processing.pipeline_mode === "mock-heuristic") {
    return "heuristic pasted-text artifact";
  }
  return "resident Codex scaffold";
}
