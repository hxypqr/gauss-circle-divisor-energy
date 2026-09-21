# A remark on first spacing in Gauss's circle problem and Dirichlet's divisor problem

Lean 4 formalization of *A remark on first spacing in Gauss's circle problem and Dirichlet's divisor problem*. The `EnergyV3` development formalizes the internal proof of the first-spacing estimate and the resulting circle and divisor error bounds, with the external mathematical inputs stated explicitly as theorem parameters.

The project uses **Lean 4.32.1** and **mathlib v4.32.1**. The supplied verification records report a successful build and an axiom audit of 2,133 exported project theorems. The Lean sources contain no `sorry`, `admit`, `native_decide`, or project-declared `axiom`.

## Main result

For every $\varepsilon>0$, the formalized conclusion is that there is a constant $C_\varepsilon>0$ such that, for every real $X\ge2$,

$$
|R(X)|\le C_\varepsilon X^{573/1828+\varepsilon},
\qquad
|\Delta(X)|\le C_\varepsilon X^{573/1828+\varepsilon}.
$$

Here

$$
R(X)=\#\{(m,n)\in\mathbb Z^2:m^2+n^2\le X\}-\pi X,
\qquad
\Delta(X)=\sum_{n\le X}d(n)-X\log X-(2\gamma-1)X.
$$

The exponent is $573/1828=0.3134573304157549\ldots$. In the circle problem, $X$ is the **squared radius**. The Lean definitions use the actual integer-point set and the actual finite sum of divisor counts.

The final theorem is conditional on the external inputs listed below. First-spacing estimates, local density bounds, fourth-moment energy bounds, and the final discrepancy reduction are proved inside the project, rather than assumed in the final theorem.

## Main results and entry points

The names in this table are in the namespace `CircleDivisor.EnergyV3`.

| Result | Lean theorem | Source |
|---|---|---|
| Circle and divisor bounds with the error functions and exponent displayed | `circle_and_divisor_error` | [Main.lean](CircleDivisor/EnergyV3/Main.lean) |
| Main theorem assembled from the external inputs | `main_of_external_inputs` | [Main.lean](CircleDivisor/EnergyV3/Main.lean) |
| First-spacing estimate, with a constant uniform in $4<q\le9/2$ | `uniformFirstSpacing_of_external_inputs` | [FirstSpacingProof.lean](CircleDivisor/EnergyV3/FirstSpacingProof.lean) |
| First-spacing estimate for each fixed $q$ | `firstSpacing_of_external_inputs` | [FirstSpacingProof.lean](CircleDivisor/EnergyV3/FirstSpacingProof.lean) |
| Square-root moment bound under the two power conditions | `Corollaries.sqrt_moment_of_external_inputs` | [Corollaries.lean](CircleDivisor/EnergyV3/Corollaries.lean) |
| The $q=9/2$ range $L^{11/7}\le K\le L^3$ | `Corollaries.nine_halves_moment_of_external_inputs` | [Corollaries.lean](CircleDivisor/EnergyV3/Corollaries.lean) |

The uniform first-spacing theorem retains the explicit factor $q/(q-4)$ and chooses its constant before quantifying over $q$. It uses only the Guth–Maldague input and the classical divisor bound.

The [proof map](ENERGY_V3_PROOF_MAP.md) gives the detailed correspondence with the manuscript. Its main components are:

- two-width integer pair counts and weighted fourth moments on the cone;
- Fourier localization, canonical caps, kernel decay, and countable envelope averages;
- local density and energy estimates, amplitude integration, and uniform first spacing;
- admissible arithmetic block construction and exact optimization with four fixed moments; and
- finite Fourier and sawtooth reductions to the actual circle and divisor errors.

## External inputs and trust boundary

The main theorem has four external proposition parameters. The fourth bundles five classical inputs, giving eight named inputs in total. Parameter names in this table are relative to the namespace `CircleDivisor`.

| Parameter | Mathematical input | Source |
|---|---|---|
| `GuthMaldague.GuthMaldagueInput` | The amplitude-dependent wave-envelope theorem for the cone, stated for the concrete functions, caps, weights, and countable sums used here | [GuthMaldagueInput.lean](CircleDivisor/GuthMaldagueInput.lean) |
| `EnergyV3.LiYangInput` | The fixed-$q$ Li–Yang arithmetic interface, with six explicit scale conditions verified by the internal construction | [ExternalArithmetic.lean](CircleDivisor/EnergyV3/ExternalArithmetic.lean) |
| `EnergyV3.ElementaryReciprocal.GrahamKolesnikInput` | The one-variable exponential-sum estimates used for reciprocal phases | [ElementaryReciprocal.lean](CircleDivisor/EnergyV3/ElementaryReciprocal.lean) |
| `ClassicalInputs.Inputs` | The two-squares coefficient formula, the Dirichlet beta value at 1, a harmonic-number remainder formula, the subpower divisor bound, and Vaaler's finite approximation | [ClassicalInputs.lean](CircleDivisor/ClassicalInputs.lean) |

These propositions are hypotheses of the final theorems, not additional Lean axiom declarations. They are not reproved in this repository. Lean checks the deductions from these hypotheses using the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. Passing an axiom audit does not remove the explicit theorem hypotheses.

The [external-input audit](ENERGY_V3_EXTERNAL_FINAL_AUDIT.md) records the exact source interfaces, normalizations, and limits of the accompanying literature checks.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run these commands from the repository root:

```text
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean verification/EnergyV3Axioms.lean
```

[lean-toolchain](lean-toolchain) pins Lean to `v4.32.1`. [lake-manifest.json](lake-manifest.json) locks mathlib to commit `520045ab14e26149ee970e2e617ca04b09bde5d6` and records the remaining dependencies.

[Audit.lean](Audit.lean) traverses the exported `CircleDivisor` theorem declarations and rejects any transitive axiom dependency outside the three standard axioms above. [EnergyV3Axioms.lean](verification/EnergyV3Axioms.lean) additionally prints dependencies for the main results and the intermediate proof branches.

The supplied [verification snapshot](verification/STATUS_ENERGY_V3.md), dated 2026-09-20, records a successful `lake build` and an audit of 2,133 exported theorems. Its build and dependency logs are preserved in [verification/](verification/). These are the verification records shipped with the source archive; publication checks are recorded separately in [PUBLICATION.md](verification/PUBLICATION.md).

## Repository layout and manuscript versions

| Path | Contents |
|---|---|
| [CircleDivisor.lean](CircleDivisor.lean) | Top-level import, including the `EnergyV3` development |
| [CircleDivisor/EnergyV3/](CircleDivisor/EnergyV3/) | The September 8 manuscript's proof and main results |
| [CircleDivisor/](CircleDivisor/) | Shared definitions, analytic infrastructure, and earlier development |
| [ENERGY_V3_PROOF_MAP.md](ENERGY_V3_PROOF_MAP.md) | Detailed manuscript-to-theorem correspondence |
| [ENERGY_V3_EXTERNAL_FINAL_AUDIT.md](ENERGY_V3_EXTERNAL_FINAL_AUDIT.md) | Current external-input audit |
| [verification/](verification/) | Build records, dependency audits, and verification instructions |
| [manuscript/](manuscript/) | Reference manuscript snapshots and supporting notes |

The reference manuscript is the **2026-09-08** version: [TeX](manuscript/Gauss_circle_divisor_energy.tex) and [PDF](manuscript/Gauss_circle_divisor_energy.pdf). These files are preserved as supplied with the formalization. A separate [submission TeX](manuscript/Gauss_circle_divisor_energy_submission.tex) contains the revised title, abstract, introductory numerical comparison, acknowledgements, AI statement, affiliation, and formatting, with corresponding citation notes updated. The theorem statements, estimates, and proofs are unchanged.

The dated [September 6 README](README_2026-09-06.md), the `ROUND2` reports, and other earlier notes document historical stages. Their incomplete-status statements and earlier exponent do not describe the `EnergyV3` main theorem. For the current proof coverage, use the `EnergyV3` proof map, final external-input audit, and [STATUS_ENERGY_V3.md](verification/STATUS_ENERGY_V3.md).
