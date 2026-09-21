# Publication checks

This repository was prepared from `CircleDivisor_EnergyV3_Lean.zip` for public distribution. It contains the `EnergyV3` formalization of the September 8 manuscript.

## Source preservation

- Archive SHA-256: `4763a8bb7d4f592478b3250f6c52e790930d1607e00163107f249e3154d06634`.
- All 107 supplied `.lean` files were compared with the archive using SHA-256 and are byte-for-byte unchanged.
- The Lean toolchain and all dependency revisions remain fixed to the supplied versions. The manifest's top-level project name was corrected from an unrelated project name to `CircleDivisor`, matching `lakefile.toml`; no dependency pin was changed.
- The original manuscript files and historical verification logs remain unchanged.
- The README was rewritten for public readers. The dated historical README retains its earlier mathematical status description, with personal attribution removed from its introduction.
- Build artifacts and downloaded dependencies are excluded by `.gitignore`.

## Manuscript files

`manuscript/Gauss_circle_divisor_energy.tex` and its accompanying PDF are the original September 8 reference snapshot.

`manuscript/Gauss_circle_divisor_energy_submission.tex` is the submission source prepared alongside publication. It revises the abstract, acknowledgements, AI-use statement, affiliation, contact information, and formatting. The mathematical body, appendices, and bibliography are unchanged from the reference snapshot. It includes the affiliation **School of Mathematical Sciences, University of Chinese Academy of Sciences** and the contact email `hxypqr@gmail.com`.

Older manuscript material is preserved for historical cross-reference; it is not the source of the `573/1828` result.

## Verification evidence

The supplied [STATUS_ENERGY_V3.md](STATUS_ENERGY_V3.md), [build log](build_energy_v3.txt), and [axiom audit](axioms_energy_v3.txt) record the original successful build and the audit of 2,133 exported theorem declarations. They are historical records, not newly generated publication logs.

A source scan of the supplied Lean files found no `sorry`, `admit`, `native_decide`, or custom `axiom` declaration. This text-level check is supplementary to the Lean audits; it does not replace compilation or kernel checking.

Publication preparation confirmed that the official mathlib `v4.32.1` tag resolves to the locked commit `520045ab14e26149ee970e2e617ca04b09bde5d6`, installed the matching Lean `v4.32.1` toolchain, and retrieved the locked dependencies and their available cache. A fresh full build and the two Lean audits were not completed during publication preparation. No new successful kernel-verification run is claimed here; the successful build and theorem-audit results cited above are the records supplied with the archive.

To reproduce the verification, install the pinned toolchain, fetch the mathlib cache, build the project, and run both supplied audit entry points using the commands in the README. An installed toolchain or an in-progress build is not evidence of a successful verification run.

The mathematical trust boundary remains the explicit external proposition parameters described in [the README](../README.md) and [the external-input audit](../ENERGY_V3_EXTERNAL_FINAL_AUDIT.md).
