What do we need to represent in our theorem prover?

* Correctly-typed terms of the core type theory. It's possible that these terms
  involve axioms.
* "Partially-constructed" terms with metavariables, used during elaboration,
  type inference, and automatic proof construction.

I'm not sure if these will be the same representation. We'll (later) need some
way to map these back to name information given by the user. This information
should be kept out-of-band.

Note that at top-level, we have axioms and definitions, which are not terms
per se. This doesn't change the representation much though: axioms are like
working under a Pi type, and definitions are like working under a Lambda (e.g.
with substitution).
