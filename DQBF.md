# Dependency QBF in pq-verify

This is the specification for the DQBF stage of the specification front end:
`pq_verify/dqbf.py`, run by the self-suite's seven DQBF checks. It was written
before the code and revised where the code showed it wrong.

## What a DQBF is

A dependency quantified Boolean formula

    ∀u₁ … uₙ  ∃x₁(D₁) … ∃xₘ(Dₘ).  φ

gives each existential variable xᵢ a dependency set Dᵢ ⊆ U = {u₁, …, uₙ}. It
is true when there are Skolem functions fᵢ : {0,1}^Dᵢ → {0,1} such that φ,
with every xᵢ replaced by fᵢ of the universals in Dᵢ, holds for every
assignment of U. Unlike a QBF, the dependency sets need not be nested, and
deciding a DQBF is NEXPTIME-complete in general.

In pq-verify the matrix φ is a conjunction of XOR constraints (a set of
variables and a parity: their sum mod 2 equals it) and clauses (a disjunction
of literals).

## What the pipeline did through 2.13.0

It answered a different question, and its answer of satisfiable said
nothing about the DQBF:

1. **Clauses constrained nothing.** Each clause became an XOR equation with
   fresh variables that nothing else constrained. A clause is not linear
   over GF(2) (x ∨ y = x ⊕ y ⊕ xy), and the fresh variable stood for the
   product with nothing tying it to it. The four clauses
   (x₁ ∨ x₂)(¬x₁ ∨ x₂)(x₁ ∨ ¬x₂)(¬x₁ ∨ ¬x₂), which no assignment satisfies,
   came back satisfiable.
2. **Universals and dependency sets were ignored.** The GF(2) solve found
   one assignment of every variable, universals included, which decides
   ∃U ∃X. φ. ∀u ∃x(∅). x ⊕ u = 0 is false, since x may not read u, and it
   came back satisfiable.
3. **The module it checked is false, and it said satisfiable.** In the
   Phase 4b module, the two XOR constraints force x₂ = k constant,
   x₁ = 1 ⊕ k ⊕ u₁ and x₃ = k ⊕ u₂, since x₁ reads only u₁ and x₃ only u₂.
   The clause x₁ ∨ x₃ then fails at u₁ = 1, u₂ = 0 when k = 0, and at
   u₁ = 0, u₂ = 1 when k = 1. All seven of its checks passed.
4. **The module parser read regular expressions, not the format.** It took
   `parity="2"` (which the engine then read as 0), ignored an element it did
   not know, accepted a dependency on an existential variable, and stopped
   with a KeyError on a misspelled `deps` or on attributes in another order.

## Decision procedures

Every answer carries a certificate, and a checker apart from the solver
verifies it from the formula. A verdict rests on the checker: an answer that
the checker rejects is a defect, raised as `CertificateError` and reported
by the self-suite as CRITICAL, never a result. Anything not decided is
CANNOT VERIFY.

### XOR matrices: affine Skolem functions

**Theorem.** If φ is a conjunction of XOR constraints, the DQBF is true if
and only if it has affine Skolem functions
fᵢ(u) = cᵢ ⊕ ⊕_{u∈Dᵢ} aᵢ,ᵤ·u.

*Proof.* Write each Skolem function in algebraic normal form, a multilinear
polynomial over GF(2) in the universals of its own Dᵢ. A constraint holds for
every assignment of U exactly when the sum of its terms is the zero
polynomial. Keeping only the terms of degree at most 1 is linear, and it
leaves the constraint's own universals and parity unchanged. So the parts of
degree at most 1 of the Skolem functions satisfy every constraint too, and
each still reads only its Dᵢ. ∎

So an XOR matrix is decided in polynomial time, by a linear system over
GF(2) in the unknowns cᵢ and aᵢ,ᵤ (u ∈ Dᵢ). A constraint with existentials
E, universals W (repeats cancelled) and parity p gives

    ⊕_{i∈E} cᵢ = p,   and for each universal u it reads:   ⊕_{i∈E, u∈Dᵢ} aᵢ,ᵤ = [u ∈ W]

where the universals it reads are W and the dependency sets of E. The system
goes to pq-verify's GF(2) engine (`libpqv_gf2`) when it fits (2048 unknowns,
8192 equations), and to an exact elimination in Python otherwise.

- **True.** The certificate is the affine functions. The checker substitutes
  them into every constraint and checks that the constant and every
  coefficient of the result vanish, which covers all 2ⁿ assignments at once,
  and that each function reads only its own dependency set.
- **False.** The certificate is a set of the system's equations whose sum is
  0 = 1. The checker builds the system from the formula again and adds them.
  With the theorem, no Skolem functions exist.

The engine is checked, not trusted: an assignment that fails the checker, or
an answer of unsatisfiable where the elimination finds a solution, is an
engine defect. An answer of unsatisfiable is confirmed by the elimination,
which also produces the refutation.

### Clauses: universal expansion

With clauses in φ no linear system decides the DQBF.

- **The XOR constraints first.** If they alone have no affine Skolem
  functions, the DQBF is false, with the same certificate as above: clauses
  only add constraints. This is found in polynomial time, whatever the size
  of the expansion.
- **Expand.** For each assignment σ of U, substitute σ into every constraint
  and replace each xᵢ by the variable x_{i,σ|Dᵢ}, which stands for fᵢ's value
  on σ restricted to Dᵢ. The DQBF is true if and only if the resulting
  propositional formula is satisfiable. A constraint's instance depends only
  on the universals it reads, so each constraint is instantiated once per
  assignment of those, which gives the same clauses as all 2ⁿ assignments.
  An XOR constraint becomes clauses: for k ≤ 3 variables, the 2ᵏ⁻¹ clauses
  that each forbid one wrong assignment; for more, a Tseitin chain of fresh
  variables t₁ = v₁ ⊕ v₂, tⱼ = tⱼ₋₁ ⊕ vⱼ₊₁.
- **Solve** with a CDCL solver (two watched literals, first-UIP learning
  with minimization, activity-ordered decisions with phase saving, Luby
  restarts) that logs every clause it learns.
- **True.** The certificate is the Skolem functions as truth tables, read
  from the model. The checker evaluates every constraint of φ, from the
  formula itself and without the expansion, on every assignment of the
  universals it reads.
- **False.** The certificate is the log, a RUP proof: every learned clause,
  and finally the empty clause, must follow by unit propagation from the
  clauses and the learned clauses before it. The checker verifies every
  step. It keeps what propagation forces from the clauses alone between
  steps, and finds the clauses to examine by two watched literals; it
  decides that a clause is unit or conflicting only by reading all of it,
  so the watches can change its speed but not its answer. The expansion and
  the clause encoding are the trusted base of this answer. Both are short,
  and both are tested against brute force.

Expansion is used while it has at most 2¹⁸ variables and clauses together,
and the solver stops after 200,000 conflicts. Beyond either, the answer is
CANNOT VERIFY.

## The module format

A module is XML, parsed by ElementTree and checked against the format:

```xml
<module name="ntt_verify">
  <vars>
    <forall vars="u1 u2" />
    <exists vars="x1" deps="u1" />
  </vars>
  <constraints>
    <xor id="c1" parity="1">x1 u1</xor>
    <or id="c2">x1 !u2</or>
  </constraints>
</module>
```

`<vars>` comes before `<constraints>`, and each appears once. `<forall>`
takes `vars`; `<exists>` takes `vars` and `deps` (`deps=""` for none); `<xor>`
takes `parity` (0 or 1) and an optional `id`; `<or>` takes an optional `id`,
and `!` negates a literal. Anything else is an error, not a skip: an unknown
element or attribute, stray text, an undeclared or doubly declared variable,
a dependency on a variable that is not universal, an empty constraint, a
repeated `id`, and a DOCTYPE or entity declaration.

## The self-suite's DQBF checks

Seven, each able to fail (the tests break each one on purpose):

1. **CFL XML parser.** The Phase 4b module parses, and six malformed
   variants are rejected: a misspelled `deps`, a dependency on an
   existential, parity 2, an undeclared variable, an unknown element, an
   `<exists>` without `deps`.
2. **DQBF conversion.** The formula's universals, existentials, dependency
   sets and constraints are the module's.
3. **Structural routing.** The module, which has clauses, goes to expansion;
   an XOR-only formula goes to affine Skolem functions; clauses over 20
   existentials that each read their own universal (2²⁰ instances each) are
   CANNOT VERIFY.
4. **Phase 4b module decided.** False, by expansion, with its RUP proof
   checked, and an enumeration of every choice of Skolem functions agrees.
5. **False formulas refuted.** ∀u ∃x(∅). x ⊕ u = 0 by affine Skolem
   functions, and the four clauses above by expansion: both false, both
   refutations checked, and enumeration agrees.
6. **Tampered certificates rejected.** Eight valid certificates, known by
   hand, are found by the procedures and accepted by the checkers, and
   fifteen tampered ones are rejected: each entry of the only Skolem table of
   y = u₁ ∧ u₂ flipped; functions that satisfy x ⊕ u = 0 by reading u outside
   an empty dependency set, as an affine function and as a table; a flipped
   affine constant; each equation dropped from a refutation that needs all
   three; and a RUP proof checked against each satisfiable three of the four
   clauses, and with its learned clause removed.
7. **1000-var DQBF stress.** 200 universals and 800 existentials, each
   reading one universal, and 1500 constraints of 2 to 4 existentials planted
   to hold under chosen affine Skolem functions: decided true on
   `libpqv_gf2` (1600 unknowns, 6001 equations) and the functions checked.

## Tests

The pytest suite checks the decisions against an enumeration of every choice
of Skolem functions on 689 random small formulas; affine Skolem functions
against expansion on XOR formulas too large to enumerate; the engine against
the elimination; the local expansion against the full one; the CDCL solver
against brute force; the RUP checker against a naive one on real and
tampered proofs; the parser on eighteen malformed modules; and the checkers
on malformed certificates, which they reject without raising.

## What it does not do

- It decides XOR matrices, and matrices with clauses while the expansion
  fits. Anything larger with clauses, unless its XOR constraints alone
  refute it, is CANNOT VERIFY. General DQBF solvers (HQS, DQBDD, Pedant)
  decide larger formulas, by other methods.
- It is research infrastructure (the research track), not evidence about any
  implementation. No post-quantum obligation is written as a DQBF yet, and
  the CFL specification path (CFL → FOL → QBF) is separate from this stage.
