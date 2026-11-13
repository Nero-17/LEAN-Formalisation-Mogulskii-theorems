# LEAN-Formalisation-Mogulskii-theorems

Lean 4 proofs of two Mogulskii theorems for random walks. Import the package with `import Mogulskii`.

| Declaration | Result |
| --- | --- |
| [`Mogulskii.pathLargeDeviation`](Mogulskii/PathTheorem.lean) | A speed-`n` large deviation principle in the uniform topology for polygonally interpolated finite-dimensional i.i.d. walks with all directional exponential moments. The good rate function is the integral of the Cramér rate along an absolutely continuous path starting at zero, and is infinite otherwise. |
| [`Mogulskii.smallDeviationStatement`](Mogulskii/SmallDeviation.lean) | Matching exponential bounds for a centered real i.i.d. walk with finite positive variance in a continuous moving tube, on scales `a n → ∞` and `a n / √n → 0`. |
| [`Mogulskii.smallDeviation_log_tendsto`](Mogulskii/SmallDeviation.lean) | The normalized log probability converges to `−(π²σ²/2) ∫₀¹ (g(t) − f(t))⁻² dt`. |

The precise statements, including the tube's initial condition and the path rate at non-absolutely-continuous paths, are in [`Mogulskii/Statements.lean`](Mogulskii/Statements.lean).

## Reproduce the proofs

Install [Elan](https://github.com/leanprover/elan), then run the following from the repository root. The toolchain file pins Lean 4.32.1. The Lake configuration pins mathlib to `520045ab14e26149ee970e2e617ca04b09bde5d6`.

```sh
lake update
lake exe cache get
lake build
lake env lean VerifyAxioms.lean
```

The axiom audit checks all three declarations transitively. Each is expected to depend only on `propext`, `Classical.choice`, and `Quot.sound`. The audit exits with an error if it finds any other axiom, including `sorryAx`.

The Brownian motion construction, Kolmogorov extension, and Donsker proof are bundled under [`vendor/`](vendor/README.md), with upstream references and license files.
