# Vendored Brownian construction

The `BrownianMotion` sources come from Rémy Degenne and collaborators' [Brownian motion formalization](https://github.com/RemyDegenne/brownian-motion/tree/4d52fa776130a29d4ad7d6eda2035a919c0b4696). The `KolmogorovExtension4` sources come from that revision's pinned [Kolmogorov extension formalization](https://github.com/RemyDegenne/kolmogorov_extension4/tree/f33cbc388e5d444606dffa7eec507a26b62c15bb). Both are distributed under Apache 2.0. Each directory contains its own upstream license.

The source subset supplies `BrownianMotion.Gaussian.BrownianMotion` and its dependencies. The project builds these sources against the mathlib revision in its root `lakefile.toml`.

# Donsker invariance principle

`MathlibExt/Probability` contains the Donsker proof and its supporting files
from [Atlas Lean](https://github.com/facebookresearch/atlas-lean/tree/9c6039404555bfc990b0e163b5740a7c87d1b4e8),
adapted for Lean 4.32.1 and this project's Mathlib pin. The Atlas revision targets
Lean 4.35.0 and [Mathlib 56a00585](https://github.com/leanprover-community/mathlib4/commit/56a005855ea17e0b0958f73ec801ae140b0a1679).
The upstream license is in `MathlibExt/LICENSE`.

