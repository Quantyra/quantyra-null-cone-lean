# Marked volume application comparison

S044, 2026-10-09. This frozen study asks whether the accepted marked-volume pipeline improves a simulator validation decision over applicable established inference. It uses the genuine 1+1 chronology of an accepted smooth density family, unknown bounded independent thinning, and the full observed order with two fixed anchors. It tests a scientific simulation use case; detector ranges are sensitivity assumptions without instrument validation.

The [protocol](protocol.json) fixes 24 known-geometry strata and 108 withheld strata. Withheld geometries and detector patterns are absent from the known phase. Both phases and all methods are frozen before any sampling; estimator functions receive only the order, anchor roles, n and R. Each stratum has 64 independently seeded trials, for 8,448 trials in total. Exact continuous-model binomial laws supply the primary coverage, width and decision metrics. Float coordinate simulation tests the observation pipeline and has a separately specified aggregate-count diagnostic.

The intended user is a simulation researcher checking a nominated interval volume to absolute tolerance 1/32. A report can support acceptance, rejection, an unresolved outcome or a model alarm. Known targets and withheld nuisance choices belong only to the evaluator. All reports use the same geometric range [1/8,3/8]. Absolute utility requires useful uncertainty and correct decisions; advancing also requires a quantitative improvement over established inference at the same information and within the declared compute ceiling.

## Comparator selection

The [complete Aronow–Lee comparison](../../notes/physical-volume-selection-comparison.md) establishes that their binary selection transforms plus the same Clopper–Pearson certificate give the existing report exactly. The implementation counts membership and constructs the reference transform separately. It shares the declared binomial calibration bank equally between methods; that bank is reverified and its generation cost is not misreported as fresh computation. No prior pilot samples or performance outputs are used.

[Fay, 2010, sections 2–3 and 9](https://journal.r-project.org/articles/RJ-2010-008/) also describes Blaker and likelihood-ordered exact intervals. The full article was inspected. Its formulas show Blaker's p-value is no greater than the central p-value, so inversion and interval hull give an interval contained in the central binomial interval. The positive monotone retention maps and common outward rounding preserve that ordering. CP is therefore not claimed shortest or globally best. These alternative endpoints are not numerically implemented here.

This sharper alternative cannot rescue an incremental width/decision claim for a candidate already identical to the eligible CP counterpart. A failure against that counterpart is sufficient to stop this candidate's application-advantage claim; it is not a positive comparison against the best conceivable method. The protocol still measures the complete pipeline, absolute scientific utility and costs. A positive advance claim would require executing the stronger applicable comparator rather than relying on this stopping argument. No such claim can be inferred from equal reports.

## Execution and evidence

Run with the repository's Python environment after committing and pushing all sources:

```text
python applications/marked-volume/benchmark.py --output applications/marked-volume/evidence/v1/attempt-1
```

The runner requires a clean worktree and matching local/remote main. It creates a new attempt directory, binds source hashes, and preserves every pre-existing tracked file. `strata.json.gz`, `trials.json.gz` and `witnesses.json.gz` are ordinary UTF-8 JSON compressed with deterministic gzip metadata. A failure remains in its own directory. Never overwrite the original S040/S041 pilot or the S046 finite comparison.

Resource limits cover the complete fresh run: 1,800 seconds, 512 MiB of Python-traced allocation and 32 MiB of new artifacts. Record calibration verification, exact laws, sampling, relation construction and method times separately. Tracemalloc omits untraced native/process memory. Relation construction is included, although both methods receive the same precomputed relation. No runtime-superiority or monetary-cost claim follows from wrapper timings.

The statistical guarantees and admissible density family reuse accepted S040/S041/S046 results; this study adds no new theorem endpoint or dimensional extension. No Lean command is run locally or as part of this benchmark. New substantive theorem claims would require separate GCP-only acceptance. The Boolean input checks reject schema, self-relation and asymmetry errors; they are not a general recognizer of every invalid causal model.

Remaining to-do list: commit/push the protocol and runner, execute the bounded study, independently audit retained evidence, and deliver S044's decision and conditional-stage disposition.
