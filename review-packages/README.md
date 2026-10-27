# Lean review packages

Six separate projects collect reusable mathematics from the RH research archive. Start with a package's essay, then its exact statements and verification record.

**These are published review snapshots.** Their unchanged source files have saved individual Lean acceptance. The newly assembled standalone projects have **not** had a clean-root build or aggregate replay. Their manually prepared root locks have not been accepted by Lake. No RH proof, new global arithmetic estimate, external peer review or current-upstream novelty is claimed.

| Package | Mathematical scope | Saved terminal axiom reports |
|---|---|---:|
| [Finite boundary gauge](finite-boundary-gauge/README.md) | Reconstruction from finite mixed differences, with boundary terms and signed weights | 10 |
| [Cumulative-prefix energy](cumulative-prefix-energy/README.md) | Exact square and bilinear integral identities for finite signed prefixes | 10 |
| [Gauss digamma integral](gauss-digamma/README.md) | Classical digamma difference formula with proved integrability | 23 |
| [Scalar EGF derivatives](scalar-egf/README.md) | Iterated differentiation with the same power-series radius | 1 |
| [Paired-measure Jensen approximation](paired-jensen/README.md) | Entire moment expansion and explicit approximation bound under Gaussian integrability | 54 |
| [Theta–Macdonald order](theta-macdonald/README.md) | Actual normalized densities: unique crossing, strict CDF and positive-integer moment order | 157 |

## Read the claims at their actual scope

Each directory includes an essay (`README.md`), unchanged Lean sources, `THEOREM-STATEMENTS.md`, `VERIFICATION.md`, source/evidence maps, pinned dependencies, a `BUILD.md` recipe, attribution, notices and a human-review checklist. The [collection manifest](COLLECTION.json) identifies all six snapshots. Each self-excluding `PAYLOAD-MANIFEST.json` fingerprints that package's other files.

All six projects pin **Lean 4.36.0-rc1** and **Mathlib c85646e3ac7d3ca39468f114b2d95d62e1611533**. The 255 saved terminal reports stay within `propext`, `Classical.choice` and `Quot.sound`. Report coverage is documented per package; this is not a separate terminal print for every helper or a new transitive replay. Some saved successful runs contain nonfatal warnings, retained in their evidence.

These are independent Lake roots, not a verified unified project. Read the relevant build prerequisites before attempting a replay; no compiler or dependency installation was run for this publication. No CI build is supplied for these snapshots. The older [finite-ledger certificates](../qrh-obstructions-lean/README.md) remain a separate project with their original pins and status.

The Jensen package concerns a difference of two positive measures with the stated Gaussian integrability. It does not supply an unproved native/Jordan signed-measure instantiation. The theta package includes the actual complete infinite source and normalization chain; it does not imply an oscillatory transform order or RH. The other packages implement classical finite algebra or analysis without claiming a new arithmetic cancellation estimate.

## Provenance and review

The package documents are frozen assembly records. Their statements that human release approval or standalone replay was pending describe those assemblies. The owner subsequently authorized hosting these review snapshots; that does not establish human mathematical approval, a fresh build, historical model identities, rights clearance or a new license grant.

Existing project MIT notices and separate Mathlib Apache-2.0 notices are retained byte-for-byte. Dependencies retain their own notices. Consult each `LICENSE-STATUS.md` and `ATTRIBUTION.md`; no new license is selected here. Preparation was AI-assisted and internal checks are not external independent review.

Only curated research payloads are included. Private raw provenance, session records, runtime diagnostics and unrelated archive material remain outside this collection.
