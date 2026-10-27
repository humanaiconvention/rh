# Complete local source boundary

The default root is `JensenMomentEntire`. Its four local import edges form this dependency chain:

`JensenMomentEntire → JensenEvenMoments → JensenGaussianMeasure → JensenPointwise → JensenWeights`.

Every local source is included unchanged. External Mathlib roots are separately pinned;their presence is not a fresh build. The [closure map](evidence/source-closure.json) records the five exact source hashes and24unique direct Mathlib modules. The source has39import occurrences:35Mathlib occurrences and4local edges. These are dependency bookkeeping,not mathematical progress.

| Source | Namespace boundary | Saved reports |
|---|---|---:|
| [JensenWeights](JensenWeights.lean) | `SignedJensenPrep` | 5 |
| [JensenPointwise](JensenPointwise.lean) | `SignedJensenKernelPrep` | 10 |
| [JensenGaussianMeasure](JensenGaussianMeasure.lean) | `SignedJensenGaussianPrep`, `SignedJensenMeasurePrep` | 15 |
| [JensenEvenMoments](JensenEvenMoments.lean) | `SignedJensenMomentsPrep` | 12 |
| [JensenMomentEntire](JensenMomentEntire.lean) | `SignedJensenEntirePrep` | 12 |

The [literal declarations](THEOREM-STATEMENTS.md) include81theorems,19definitions and one type abbreviation. The [roster](evidence/public-declarations.json) identifies54saved terminal reports and27other compiled theorems without separate historical prints. The two different `momentCoefficient` definitions retain their actual namespaces and roles. Existing preparation comments/reference paths are historical context,not additional imports or portable provider requirements.
