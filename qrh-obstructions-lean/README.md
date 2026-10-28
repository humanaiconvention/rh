# Lean certificates for analytic obstructions and local phase survival

This repository provides **two machine-verified Lean 4 certificates**:

- **Analytic obstructions:** three mathematical obstructions to taking a
  specified continuous analytic architecture unchanged to
  $\operatorname{Re}(s)=1/2$, in `Obstructions.lean`.
- **Local metaplectic phase survival:** exact algebraic nonvanishing of
  the combined phase of the conjugate norm-157 slot, under its stated
  unit-phase cube relation, in `MetaplecticDictionary.lean`.

Here QRH refers to the audited quasi-Riemann-hypothesis architecture.

The proofs are complete: there are no admitted lemmas or added
mathematical axioms. The compiler's dependency audit reports only the
standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.
The formalization includes the prime-ideal divergence argument.

## Certificate 1: analytic obstructions

### 1. Euler-defect non-summability

For a positive real prime norm $Q$, complex $x$ with
$\sigma=\operatorname{Re}(x)$, and unit complex phases $\eta,a$, define

$$
v=Q^{-1},\qquad D=\eta Q^{-x},\qquad R=a^2Q^{3-6x},
$$

$$
H_Q=(1-v^2)\left(\frac{v}{1-D}+\frac{1-v}{1-R}\right).
$$

Complex powers use the positive real base $Q$. The phase $a$ is the
combined local phase; it need not satisfy any independence assumption.
The file proves the uniform local estimate

$$
\|H_Q-1\|\ge\frac14 Q^{3-6\sigma}
\qquad
(Q\ge64,\;1/2<\sigma\le2/3).
$$

Let $K=\mathbb Q(\omega)$, with $\omega$ a primitive cube root of unity.
For its nonzero prime ideals, $Q$ is the absolute ideal norm. For every
fixed finite excluded set $S$, and any prescribed unit phases at the
remaining primes, the file proves

$$
\neg\operatorname{Summable}
\left(\mathfrak p\longmapsto\|H_{N\mathfrak p}-1\|\right),
\qquad \mathfrak p\notin S.
$$

This is a failure of the specified product's **normal absolute
convergence**. The norm cutoff $64$ is explicit in the supporting
estimate; the final non-summability theorem concerns the full prime
family outside $S$.

The supporting prime-ideal theorem is proved for every number field.
The argument combines exact ideal factorization, summability of finite
products, ideal-count asymptotics, and Tannery's theorem. Those imported
results are proved in the pinned mathlib dependency. No assumption about
L-function zeros is used.

At $\sigma=1/2$, a separate verified statement gives $\|R^n\|=1$ for
every natural $n$. The displayed defect estimate is **not** asserted for
all $\sigma\le2/3$.

### 2. The exact $3/8$ exponent deficit

For the supplied geometry,

$$
L_{\rm lo}=\frac3{16},\qquad C_{\rm II}(\sigma)=\sigma-\frac{11}{16}.
$$

The file proves

$$
L_{\rm lo}-C_{\rm II}(1/2)=\frac38.
$$

This is an arithmetic comparison of the supplied exponents. It is not a
lower bound on the actual physical mass.

### 3. The sieve-parameter collapse

With $\kappa(\beta)=2\beta-1$, the file proves

$$
\kappa(1/2)=0\notin[3/4,1].
$$

It also proves that $\kappa(\beta)$ belongs to the stipulated moment
interval exactly when $\beta\in[7/8,1]$. This records a parameter
mismatch; it does not assert that a published sieve inequality is false.

## Certificate 2: local metaplectic phase survival

[`MetaplecticDictionary.lean`](MetaplecticDictionary.lean) formalizes the
conjugate slot in the concrete Eisenstein ring $\mathbb Z[\omega]$, where
$\omega=(-1+i\sqrt3)/2$ and $\omega^2+\omega+1=0$:

$$
p=13+12\omega,\qquad \bar p=1-12\omega.
$$

The file proves conjugacy, both arithmetic norms equal to $157$, and
$p^2=-59+84\sqrt3\,i$. Here the arithmetic norm is the squared complex
absolute value. Set $\alpha=p/\sqrt{157}$ and take any phase $u_p$ with

$$
|u_p|=1,\qquad u_p^3=\overline\alpha^{\,2},\qquad
u_{\bar p}=\overline{u_p}.
$$

For the real combined phase $x=u_p+u_{\bar p}$, Lean proves

$$
157x^3-471x+118=0,\qquad
\frac{118}{471}\le |x|\le2.
$$

Thus **the combined phase is strictly nonzero**. The proof applies to
every phase satisfying the displayed relations; it does not depend on
choosing a particular cubic-root branch. Existence of such a unit phase
is also proved.

For the regularization interpretation, if the combined leading Gaussian
coefficient has the retained form $B=Kx$ with $K\ne0$, this certificate
supplies the nonvanishing of its phase factor, hence $B\ne0$. The Lean
file does **not** encode the Gaussian coefficient, derive the native
Gauss-sum cube relation, or model the regularization operation. Those
identifications remain outside this algebraic certificate. It does not
give a lower bound for the complete physical row.

See [the phase-certificate notes](MetaplecticDictionary.md) for the exact
definitions, proof outline, and scope.

## Where to find the proofs

The analytic obstruction declarations are in `Obstructions.lean`. The
principal names in the namespace `RHArchitectureObstructions` are:

| Result | Lean declaration |
| --- | --- |
| Local Euler lower bound | `principal_euler_defect_lower_bound` |
| Prime-ideal harmonic divergence with finite exclusions | `eisenstein_prime_reciprocal_unbounded` |
| Full prime-family defect non-summability | `principal_all_prime_defects_not_summable` |
| Physical exponent deficit | `physical_deficit_at_half` |
| Moment-parameter mismatch | `half_outside_proved_moment_range` |

The general number-field argument is in the namespace
`PrimeIdealDivergence`. Both the lower-bound hypotheses and the finite
exclusions are present in the formal theorem statements.
In particular, `PrimeIdealDivergence.prime_reciprocals_not_summable` can
be reused independently of the architecture-specific definitions.

For a focused reusable interface, read the [number-field divergence guide](PrimeIdealDivergence.md),
[exact selected API](PrimeIdealDivergenceAPI.md), and
[source/axiom evidence map](PRIME-IDEAL-EVIDENCE.json). They spell out the ideal
norms, finite-exclusion quantifiers and proof dependencies without copying the
source into a new project. The generic helper has historical whole-module
acceptance and downstream audit reachability, rather than a dedicated saved
helper axiom report. Public-wrapper acceptance is tied to its own matching
source-hash record; no fresh verification was run for these documents.

The local phase declarations are in the namespace
`MetaplecticDictionary`:

| Result | Lean declaration |
| --- | --- |
| Polynomial for every admissible phase | `phase_polynomial` |
| Quantitative positive lower bound | `phase_lower_bound` |
| Nonvanishing of the conjugate-pair sum | `phase_nonzero` |
| Polynomial for the selected witness | `survival_polynomial` |
| Both bounds for the selected witness | `survival_bounds` |
| Nonvanishing for the selected witness | `combined_phase_nonzero` |

## Scope and limitations

The first certificate concerns the **specified Euler factor, supplied
geometry, and stipulated moment interval**. It does not formalize the
source's original low-side analytic estimate or its moment theorem.
It does not establish RH or certify a claimed zero-free half-plane.

In particular, Euler-defect non-summability does not exclude conditional
products, further factorization, or alternative analytic continuation.
The fixed exponent and parameter calculations do not exclude different
probes, retuned geometry, or stronger moment estimates.

These are formalized obstructions to an unchanged substitution, not a
general impossibility theorem for analytic approaches.

The second certificate concerns the **exact conjugate-slot phase
algebra**. Its application to a native Gaussian coefficient requires
the external identification described above. Neither certificate
resolves RH.

The architectural context is OpenAI's manuscript
[*The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8*](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
dated 30 September 2026. This reference supplies provenance, not
certification of that manuscript's main claim. The build does not
require a copy of the manuscript or any internal research notes.

## Reproduce

Prerequisites: Git and [Elan](https://github.com/leanprover/elan), Lean's
toolchain manager. Python 3 is optional for the report audit.

The exact versions are:

- **Lean 4.35.0**, specified in `lean-toolchain`.
- **mathlib commit `6015dbbfc399f4548bafd46f9560ff61595fd328`**, specified
  in `lakefile.lean` and locked with its dependencies in
  `lake-manifest.json`.

From a fresh checkout:

```sh
git clone https://github.com/humanaiconvention/rh.git
cd rh/qrh-obstructions-lean
elan toolchain install leanprover/lean4:v4.35.0
lake update
lake exe cache get
lake build --wfail
lake env lean Obstructions.lean
lake env lean MetaplecticDictionary.lean
```

The standalone compiler commands are:

```sh
lake env lean Obstructions.lean
lake env lean MetaplecticDictionary.lean
```

To rebuild and audit the source hash, pinned dependencies, and allowed
axioms:

```sh
python scripts/verify.py
python scripts/verify_metaplectic.py
```

On systems whose Python executable is named `python3`, use that name.
The audit uses only Python's standard library. Open this repository
directory in VS Code to use the Lean extension.

Lake reads **`lean-toolchain`**. The requested `lake-toolchain` is
included as an identical compatibility copy; the audit checks both.
Cached build products and dependencies are excluded from Git.

## Verification and CI

Each certificate has its own compiler and axiom-audit records:

| Source | Verification report | Compiler log |
| --- | --- | --- |
| `Obstructions.lean` | [`VERIFICATION.json`](VERIFICATION.json) | [`VERIFICATION.log`](VERIFICATION.log) |
| `MetaplecticDictionary.lean` | [`METAPLECTIC-VERIFICATION.json`](METAPLECTIC-VERIFICATION.json) | [`METAPLECTIC-VERIFICATION.log`](METAPLECTIC-VERIFICATION.log) |

The reports identify the exact source hashes and pinned dependency.
A saved report certifies its recorded bytes; edited sources must be
checked again. The local phase record audits twelve declarations, with
zero admitted proofs and no added mathematical axioms.

The accepted earlier report is preserved verbatim at
`provenance/VERIFICATION.original.json`. Public packaging updates the
explanatory comments and adds Lean 4.35's public module/export wrapper.
Definitions, theorem statements, and proof bodies are unchanged. The
proof-code hash, normalized only for comments, whitespace, and that
wrapper, connects the two versions.

GitHub Actions installs the pinned Lean toolchain, retrieves the pinned
mathlib cache, builds with warnings treated as failures, executes the
standalone compiler commands, and audits both resulting outputs. Action
references are pinned to commit hashes. The workflow is installed at the
parent repository's `.github/workflows/lean-certificates.yml`; see
[its hosted runs](https://github.com/humanaiconvention/rh/actions/workflows/lean-certificates.yml).

## Citation and license

`CITATION.cff` supplies software citation metadata for version 0.1.0.
The credited software author is the project entity **humanaiconvention**.
Its public source is [humanaiconvention/rh](https://github.com/humanaiconvention/rh),
under `qrh-obstructions-lean`. No DOI is asserted.

Repository code and documentation are licensed under MIT; see
`LICENSE`. mathlib and other dependencies retain their own licenses.
