# API fit and dated overlap review

The candidate packages a scalar factorial-coefficient conclusion of existing analytic differentiation machinery. It does not replace Mathlib's broader Frechet/Taylor APIs. Its utility is that one explicit scalar premise yields `c(n+k)/n!` on the original representation ball without exposing helper rows.

The saved23October2026 API inspection was pinned to Mathlib `c85646e3ac7d3ca39468f114b2d95d62e1611533`. It identified `HasFPowerSeriesOnBall.fderiv`, `FormalMultilinearSeries.derivSeries_coeff_one`, scalar coefficient identities and an existing evaluation-at-one pattern. The proof actually uses that infrastructure,then factorial cancellation and induction. The inspection did not establish global absence of an equivalent convenience theorem or its present upstream status. No fresh upstream query or novelty search occurred here.

One public theorem and two private helpers is the preserved API boundary. The `module`, `public import` and `public section` syntax is part of the accepted file. Renaming,generalizing the center/scalar/target,changing visibility or source headers,and removing imports all need separate review and replay. No such cleanup or additional example theorem was introduced.

The retained historical uncompiled header and original relative attribution pointer are explained in [provenance](PROVENANCE.md). Human review should decide whether this convenience result earns a public API beside existing Frechet/Taylor results. That decision is not settled by compilation. This package contains no submission text,public branch or automatic successor.
