# CFL in pq-verify

The CFL front end turns a specification into obligations that pq-verify's
engines discharge:

    CFL text → tokens → AST → checked properties → FOL obligations
             → QBF, decided by the DQBF stage → field router → engine checks

Paper 2 ([10.5281/zenodo.19302050](https://doi.org/10.5281/zenodo.19302050))
introduced it. This page defines the language and each stage as
`pq_verify/cfl.py` and the self-suite implement them. It was written before
the code and revised where the code showed it wrong.

## What it did through 2.13.0

- **The lexer dropped any character it did not know.**
- **The parser walked tokens by position.** REQUIRE's closing brace ended its
  CONTEXT, so a DEFINE after a REQUIRE was dropped without a word, and input
  that ended early raised IndexError.
- **FOL formulas were strings, and "prenex" form was not.** The step stopped
  at the first nested quantifier, so ∀c (A → ∃p B) kept ∃p inside its
  matrix, and the result was not a QBF: its atoms were first-order
  predicates that nothing decided.
- **The router searched the whole FOL string** for a field's name, so a
  context or property whose name contained one routed by its name.
- **Dispatch solved five fixed systems**, one per engine, whatever the
  specification said; Engine 6's ran one check per engine, whatever the
  property.
- **Their checks counted** tokens, contexts and formulas, and the CFL
  benchmark passed unconditionally.

## The language

    spec     = { context } EOF
    context  = "CONTEXT" "(" IDENT ")" "{" { define | require } "}"
    define   = "DEFINE" "property" "<" IDENT ">" "{" { IDENT ":" STRING ";" } "}"
    require  = "REQUIRE" IDENT "{" [ IDENT { "," IDENT } ] "}"

IDENT is `[A-Za-z_][A-Za-z0-9_]*`, and CONTEXT, DEFINE, REQUIRE and property
are reserved. STRING is `"…"` on one line, without escapes. `//` starts a
comment that runs to the end of the line. Any other character is an error,
with its line and column.

A property has exactly two attributes, `type` and `field`. Its field names
the algebra its check runs in, and so its engine; its type must be one that
engine decides:

| field | engine | types |
|---|---|---|
| `Z_3329` | Zq (16-bit) | linear |
| `Z_8380417` | Zq32 | linear |
| `GF2` | GF(2) | linear |
| `cubic` | cubic | cubic |
| `conformity` | conformity | dynamical |
| `period` | Engine 6 | algebraic, rank, residue |

`REQUIRE Full { P, … }` names the properties of its context that are
required; `{ }` names all of them. A context with no REQUIRE requires all of
its properties. Full is the only level. Paper 2 may define more levels or
attributes; until they are defined here, each is an error.

## Stages

1. **Lexer.** Tokens with their line and column.
2. **Parser.** Recursive descent over the grammar. An error names the line,
   the column, what was expected and what was found. `to_text` prints an AST
   back as CFL, and parsing that gives the same AST.
3. **Checker.** Every problem is reported, each with its position: a context
   or property defined twice, an attribute missing, given twice or unknown,
   an unknown field, a type the field's engine does not decide, an unknown
   level, and REQUIRE naming a property its context does not define.
4. **FOL.** Formulas as an AST (∀, ∃, ¬, ∧, ∨, →, and predicates over
   variables and constants). Each required property P of context C with
   field F has the obligation

       ∀c (Ctx(c, C) → ∃p (Prop(c, p, P) ∧ Field(p, F) ∧ Verified(p)))

   Prenex form: implications removed, negations pushed to the predicates,
   bound variables renamed apart, then every quantifier pulled to the
   front. That is equivalent over every nonempty domain, and the obligation
   becomes ∀c ∃p (¬Ctx(c, C) ∨ (Prop(c, p, P) ∧ Field(p, F) ∧ Verified(p))).
5. **QBF.** A specification defines a finite model: its contexts and
   properties are the domain, the relations Ctx, Prop and Field come from
   the AST, and Verified holds of the properties whose checks passed at
   dispatch. A closed formula over a finite model becomes a QBF: each
   variable of its prenex form is k bits, enough for the domain; universals
   are restricted to the domain and existentials must choose in it; and each
   atom's truth table and each connective is defined by a fresh existential
   (Tseitin) depending on every universal. It is written as a DQBF, each
   existential depending on the universals before it, and decided by the
   DQBF stage ([DQBF.md](DQBF.md)) with its certificate checked. The answer
   must equal the formula evaluated directly on the model: a disagreement is
   a CRITICAL finding.
6. **Router.** A property goes to the engine of its parsed field.
7. **Dispatch.** Each property's registered check runs on its engine, and
   runs again on an instance made wrong on purpose, which it must reject. A
   property with no registered check, or whose engine is not built, cannot
   be verified; a declared field other than its check's is a failure.

## Obligations

| Property | Check | Made wrong |
|---|---|---|
| Kyber.NTTCorrect | the seven layers of an ML-KEM NTT, each solved on the Zq engine, composing to FIPS 203 Algorithm 9 | an output of layer 4 off by one |
| Kyber.KeygenValid | 50 invertible systems A·s = t − e: the Zq engine returns each secret | one right-hand side off by one |
| Dilithium.NTTCorrect | the eight layers of an ML-DSA NTT on the Zq32 engine, composing to FIPS 204 Algorithm 41 | an output of layer 6 off by one |
| AES.SboxAffine | S(x) = A·x⁻¹ + c solved on the GF(2) engine for all 256 inputs: a permutation with no fixed or opposite fixed point, equal to FIPS 197 at six inputs | one bit of the affine matrix flipped |
| Curves.J0Count | the cubic engine's count of x³ + y³ + z³ = 0 over F_p, p² + (p − 1)·B(a, b), equal to a direct count for eight primes p ≡ 1 mod 3 | one expected count off by one |
| Curves.Conformity | the conformity engine on ω = exp(−t²/2) at four points: u = −t and D = 2u′ + 4u² | one closed form off by 10⁻⁶ |
| Paper7.Theorem1 | Engine 6's Theorem 1, entry-wise, at rank 2, genus 2, the mirror quintic and genus 4 | a tolerance below its residuals |
| Paper7.Observation4 | the odd power traces of [U, Q] vanish at genus 2, the mirror quintic and genus 4 | a tolerance below its residuals |
| Paper7.Conjecture6 | f2, f4, f6, f8 at seven genus-4 points have rank 4 | three of the seven points |
| Paper7.Conjecture7 | Res(f4)/Res(f2) of the mirror quintic is λ₂ at z = 0 and z = 1/3125, in exact rationals (SymPy) | λ₂ off by one |

## The self-suite's CFL checks

The CFL front end (6), the CFL benchmark (1) and Engine 6 through the CFL
front end (6), each able to fail (the tests break each one on purpose):

1. **Lexer.** The specification lexes, and three malformed inputs are
   rejected with a position: an unknown character, an unclosed string, a
   backslash.
2. **Parser.** The AST is the expected one and survives a round trip; a
   DEFINE after a REQUIRE is kept; thirteen malformed specifications are
   rejected with a position, five by the parser and eight by the checker.
3. **FOL generation.** One closed obligation per required property, and
   each prenex form, and one that needs renaming apart, equal to the
   original on random models.
4. **QBF encoder.** Each obligation decided by the DQBF stage, its
   certificate checked, equal to the model and to its dispatch result; and
   two made false, an unverified property and a wrong field, decided false.
5. **Field router.** Each property's engine is its field's; names that
   contain other fields' names route by their field.
6. **Engine dispatch.** Each obligation passes, and fails when made wrong.
7. **Benchmark (`Python CFL pipeline ×100`).** A hundred runs give the same
   AST, properties and obligations, and the printed AST parses to itself.
   Each run also takes a random one-character edit of the specification
   (a character deleted, inserted or replaced). The pipeline must reject it
   with a line and column, or accept it as a specification that prints back
   to itself with closed obligations; a crash, or an error without a
   position, fails the check. A C build of the pipeline can still be loaded
   by absolute path (`PQV_CFL_SO`) to time against it; its answer is
   reported, not checked.

## What it does not do

- It verifies the obligations registered for it, each by a fixed check on
  chosen inputs, and none of them is evidence about a vendor's library: the
  vendor audits are separate. The CFL front end is research infrastructure.
- Its first-order logic has no function symbols or equality, and models are
  finite: the QBF encoding is exact for those, not a decision procedure for
  first-order logic.
