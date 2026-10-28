# Attribution and review boundary

The mathematical argument is classical: center a Lipschitz test at a signed crossing, cancel the constant by zero total mass, and bound the remaining pairing by the coordinate moment. This packet offers an explicit formal interface; it does not claim discovery of the underlying comparison or absence of an equivalent upstream theorem.

The proof reuses Mathlib's Bochner integral, Lipschitz composition and algebraic infrastructure through the imports listed in [VERIFICATION.md](VERIFICATION.md). Dependency acknowledgments do not assign coauthorship of this contribution.

Preparation and proof development were AI-assisted. Exact historical model identities and individual human contribution credits have not been authenticated. No model identity, copyright holder, contributor approval, human mathematical review or upstream maintainer approval is inferred from compilation evidence.

The unchanged source has no finalized contribution copyright/license header. Repository licensing intent does not itself establish rights in every contribution or relicense Mathlib. Imported Mathlib work retains its applicable notices and Apache 2.0 terms.

Before submission or release, review the contribution attribution and rights, notices, current-upstream overlap, API names and placement, and exact hypotheses. In particular, do not add AE measurability to the two contracts that omit it, remove it from composition contracts, replace the non-strict AE sign condition by an unstated strict crossing, restrict the final budget to nonnegative B, or omit degenerate cases. Saved acceptance does not replace these review gates or a separately chosen fresh replay.
