# Frozen Mathlib-only statement — not a proof

[Challenge.lean](Challenge.lean) retains SHA256 `089d79f22567db09aac20b42e54d0992876ddf5ebbe260fa6e68d699abc91cca` byte-for-byte. It imports only two Mathlib modules and no solution/provider. Its two `sorry` bodies are intentional specification placeholders.

It is outside the three default proof libraries and is not imported by them. Source review/freeze is historical; fresh rc1 elaboration and comparison are NOT RUN. Compiling this specification would not prove its claims, and its deliberate holes are never accepted solution axioms.

A qualified replay must independently elaborate these signatures/definitions, compare actual solution types and audit the solution's transitive axioms. The typed consumer is useful but does not replace that independent statement check. Strict isolated comparison and a compiling-but-mismatched statement control remain pending.
