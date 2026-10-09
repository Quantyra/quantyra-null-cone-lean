# S031 frozen pilot results

2026-10-08. The prescribed ten-sample pilot is complete: **all thirty estimator reports pass their exact checkers, and all thirty have maximum and mean density-band width one**. Neither local-mass candidate improves on the no-data band. The conditional eighty-sample confirmation stage is **not run**. The [decision](finite-data-feasibility-decision.md) selects theoretical continuation on the separate ordinary degree-trimming proof, not practical success of the tested estimators.

Authoritative evidence: [terminal manifest](../evidence/finite-data/feasibility-v1/manifest.json), [unchanged terminal runner manifest](../evidence/finite-data/feasibility-v1/pilot-run-manifest.json), [aggregate audit with every row](../evidence/finite-data/feasibility-v1/pilot-audit.json), and [evidence/reproduction guide](../evidence/finite-data/feasibility-v1/README.md). Frozen source revision: `9b040c5452ba87e57cb33228a07267020cc9359c`. The [version-1 protocol](finite-data-feasibility-protocol.json) retains SHA-256 `14dd9bd81f7b73dd8ae57f73047f8ad715631cb64ae68376ec7bf2c4697475f3`.

## Samples and diagnostics

Five prespecified densities each contribute one order at n=512 and one at n=3072. Bernstein, exact-binomial and the existing split-DKW baseline receive the same serialized order in each case. There are ten independent synthetic samples, not thirty independent samples. The two candidate procedures retain separate 95% coverage arguments; their outputs are not intersected. The mesh is k=8 throughout. All pilot seeds, generated-order hashes, code/dependency identities and raw outputs are retained.

| Method | n | Reports checked | Analytic joint coverage | Width <=0.90 | Max/mean point width | Reported global error radius |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| Bernstein | 512 | 5/5 | 5/5 | 0/5 | 1 / 1 in every model | 1/2 |
| Bernstein | 3072 | 5/5 | 5/5 | 0/5 | 1 / 1 in every model | 1/2 |
| Exact binomial | 512 | 5/5 | 5/5 | 0/5 | 1 / 1 in every model | 1/2 |
| Exact binomial | 3072 | 5/5 | 5/5 | 0/5 | 1 / 1 in every model | 1/2 |
| Existing split-DKW | 512 | 5/5 | 5/5 | 0/5 | 1 / 1 in every model | 1 |
| Existing split-DKW | 3072 | 5/5 | 5/5 | 0/5 | 1 / 1 in every model | 1 |

Every row's count aggregates five different fixed models and is descriptive. Coverage uses exact polynomial cell extrema/integrals over the full square, with one global orientation for all reported guarantees. It is not a dense-grid approximation or a proof of uniform statistical coverage. There are no estimator fallbacks, checker rejections, timeouts or RSS failures in these forty preparation/method runs. Expected small-limit failures in resource preflight are separate enforcement tests.

The fraction of cells meeting width <=0.90 is zero in every report, so there are no informative-output coverage observations. For each model/size/method, the one observed coverage success has exact two-sided 95% binomial interval `[1/40,1]`; the zero width-target successes have interval `[0,39/40]`. Do not pool heterogeneous models into a common binomial success probability. No conditional coverage claim is inferred from these diagnostics.

The candidates use the midpoint of their point bands, which is the flat function 1 in every case. Their radius 1/2 is exactly the no-data comparator. The baseline retains its original radius-one semantics; merely reducing that reported number to the already-known flat radius is not informative density reconstruction. Actual sup-norm errors, in **each** global orientation and for **every** method/size, are:

| Density | Actual error |
| --- | ---: |
| Flat | 0 |
| FGM, coefficient -1/2 | 1/2 |
| FGM, coefficient +1/2 | 1/2 |
| Asymmetric, coefficient -1/4 | 1/4 |
| Asymmetric, coefficient +1/4 | 1/4 |

The formulas' full-K membership and the analytic evaluator are established in the [prerequisite audit](finite-data-feasibility-prerequisites.md). Finite-precision pseudorandom simulation is an approximation to the theorem's iid experiment; its apparent coverage cannot replace the ordinary coverage proof.

## Exact explanation inside the retained LP

The aggregate auditor constructs two rational cell-average vectors for every local-mass report:

    g_i = 1-2i/(k-1),
    z^+_(i,j) = 1+(1/4)g_i g_j,
    z^-_(i,j) = 1-(1/4)g_i g_j.

All twenty witness pairs satisfy every corresponding LP inequality, row/column equality and box restriction exactly. Their corner averages are 3/4 and 5/4. Any sound outer LP interval must therefore contain both values. The fixed point expansion is 2/k=1/4, so that corner's point band must cover [1/2,3/2] and have width one. This proves a limitation of the **retained relaxation plus expansion on these inputs**, beyond observing a particular solver output. These are relaxation witnesses; no claim that arbitrary feasible vectors extend to smooth K densities is needed.

Each report has 63 or 64 of its 64 mass intervals containing the entire prior cell-mass range `[1/(2k²),3/(2k²)]`. The local concentration variants therefore add little usable restriction in this pilot. The witness argument does not bound every possible estimator's performance or make the n=3072 practical target impossible. The independent [information lower bound](finite-data-information-limit.md), about 0.0224 at n=3072, is far below the practical radius target 0.45.

## Resources and confirmation gate

Every worker includes imports, construction or estimation, serialization, independent artifact reload/check and analytic diagnostics within its measured wall time. Children are prohibited; OS peak working set measures the complete allowed process tree. The watchdog checks every 10 ms and rejects RSS overshoot. A distinct Job Object committed-memory limit is also enforced.

| Worker | Runs | Summed seconds | Longest run, seconds | Largest peak RSS, GiB |
| --- | ---: | ---: | ---: | ---: |
| Order preparation | 10 | 146.607 | 31.934 | 0.279 |
| Bernstein | 10 | 1311.975 | 380.428 | 1.671 |
| Exact binomial | 10 | 1138.055 | 287.836 | 1.997 |
| Split-DKW | 10 | 1145.035 | 288.359 | 1.999 |

The reconciled pilot ledger, including resource probes, is **3743.335 seconds** (about 1.040 hours). Adding the retained standalone certificate checks, aggregate audit and dependency-file hash scan gives **3831.369 seconds** (about 1.064 hours). No statistical sample is added by validation. All experiment runs remain below 600 seconds and 4 GiB RSS; the total remains below the 12-hour ceiling. Reports use 1,355,993–58,025,913 uncompressed bytes including their shared forcing certificate, excluding the separately recorded input order. Input/report size checks pass.

The frozen linear timing projection for eighty paired confirmation samples, including preparation, one candidate and baseline, is 20,828.933 seconds for Bernstein or 19,437.578 seconds for exact binomial. Including the pilot gives 24,572.268 or 23,180.913 seconds, both below 43,200 seconds. A projection from one trial per model/size is not a runtime guarantee.

Thus **resources are not the reason to stop confirmation**. Both candidates produced full-width bands in every pilot case, and exact feasible LP witnesses explain a worst-cell obstruction in every retained candidate report. No candidate is selected for confirmation; all eighty fresh confirmation samples remain ungenerated. The >=6/8 practical success condition is untested, not passed or statistically disproved. The stage stops at its explicit “if warranted” gate. No tuning, seed, mesh, density, cap or protocol amendment follows these results. No oracle run or memory-profile repeat is included.

## Verification and separate theoretical outcome

The 24 pre-pilot regression tests pass, including exhaustive small-order realizers, binomial endpoint coverage, corruption/boundary cases and shared-artifact rejection. Every worker reloads and independently verifies its serialized report; additional standard-library-only checks pass for one retained report of each method. The aggregate audit checks all sample identities, pairing, source/protocol hashes, artifact sizes/hashes, resource accounting and exact LP witnesses. Dependency-file and preservation receipts are described in the evidence guide.

The separate [degree-trimming proof](finite-data-interior-degree-rate.md), committed as `a397b4a98fbae822e416ca85f1cc9914cf862564`, supplies an ordinary order-only fourth-root guarantee with explicit confidence and constants. Sixteen rational constant checks pass; 96 selected accepted source identities remain unchanged. The new construction is not this pilot's estimator and has no new Lean acceptance. Its theoretical improvement, together with the same-class lower benchmark, supports the separately scoped S032 certification proposal. No existing published artifact is revised.

Remaining to-do list: none for S031's mathematical/numerical assessment. Repository delivery closes separately in the planning audit; S032 remains proposed and manuscript work deferred.
