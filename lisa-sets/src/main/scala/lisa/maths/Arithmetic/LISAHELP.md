
# LISA Proof-Scripting Field Guide (Notes for Future Agents)

This document collects practical lessons learned when writing proofs in LISA’s Scala proof DSL.
It focuses on what tends to *work reliably*, what tends to break (often subtly), and patterns that make proofs maintainable.

For the short checklist-style version (naming/style conventions + compressed best practices), see `STYLE.md`.

The examples are schematic: replace variables/lemmas with whatever your development imports.

---

## 1) Mental Model: sequents, steps, and the kernel

- A proof is a sequence of **sequent**-producing steps: `Γ |- Δ`.
- Tactics (`Tautology`, `Cut`, `RightForall`, …) build an `SCProof` under the hood.

Practical implication:

- Treat the *exact* left/right context of sequents as part of the proof state.
- When the kernel complains about a premise mismatch, the fix is almost always: ensure the premises you feed into a tactic have **exactly the sequent shape** it expects.

---

## 2) Core syntax you use constantly


### Variables

```scala
private val A, R = variable[Set]
private val x, y, z = variable[Set]
private val F = variable[Set >>: Set >>: Set] // curried F(x)(y)
private val G = variable[Set]
```

### Lambda / bounded quantifiers

- LISA uses `λ(x, P(x))` for lambda.
- Bounded quantifiers are usually encoded with implication:

```scala
∀(x ∈ A, P(x))    // syntactic sugar for ∀(x, x ∈ A ==> P(x))
∃(x ∈ A, P(x))    // similarly
```

### Epsilon terms

- `ε(x, P(x))` picks a witness if one exists.
- To use it safely, pair it with `Quantifiers.existsEpsilon` and a proof of existence.

```scala
val ex = have(∃(x, P(x))).by(...)
val a = ε(x, P(x))
val aHasP = have(P(a)).by(Cut(ex, Quantifiers.existsEpsilon.of(x := x, P := λ(x, P(x)))))
```

---

## 3) Proof structure patterns that scale

### `Theorem(...) { ... }` + local lemmas

Use `val foo = have(sequent).by(...)` to name intermediate results; it drastically improves debuggability.

### `assume` adds local hypotheses

When you need to prove `Γ, H |- Δ`, use `assume(H)` to add `H` to the context.

```scala
have(H |- goal) subproof {
    assume(H)
    // derive goal under H
    have(goal).by(...)
}
```
Concretely, assuming `H` adds it to the LHS of the sequent for all subsequent steps in the proof.

### Subproof blocks

Use `subproof { ... }` when you need assumptions local to a derivation.

```scala
val step = have(Γ |- P ==> Q) subproof {
	assume(P)
	have(Q).by(...)
	thenHave(thesis).by(Restate)
}
```

Key point: subproofs import earlier steps. If the imported sequent differs (even by extra assumptions), you can get errors.

---

## 4) Common tactics
### “Sequent shaping” is important: Restate

Many tactics are strict about the exact sequent they consume/produce.
Use `Restate` to coerce a goal into the form a tactic expects, without changing meaning. `Restate` can efficiently justify many syntactic transformations and easy logical steps. This includes:
- Commutativity of `/\` and `\/`
```scala
have (P ∧ Q).by(...)
thenHave (Q ∧ P).by(Restate)
```
- Negation normal form
```scala
have (!!P).by(...)
thenHave (P).by(Restate)
```
- Unfolding logical connectors: `==>`, `<=>`, `∃`
```scala
have (P ==> ∃(x, Q(x))).by(...)
thenHave (!P \/ ∃(x, Q(x))).by(Restate)
thenHave (!P \/ !∀(x, !Q(x))).by(Restate)
```
- Reflexivity and symmetry of `===`
```scala
have (f(c, x) = f(c, x)).by(Restate)
```
- Implication introduction/elimination

```scala
have(P  |-> Q).by(Restate)
thenHave(P ==> Q).by(Restate)
```
- Alpha renaming of bound variables
```scala
have(∀(x, P(x))).by(...)
thenHave(∀(y, P(y))).by(Restate)
```

Note that all these transformations are accepted by Restate without extra proof work, and they can be arbitrarily combined in one step, even deep in formulas.

To add assumptions, use `Weakening`.

If you have `Γ |- Δ` but need `(Γ, H) |- Δ`, add `H` with weakening.

```scala
val s1: ProofStep = have(Γ |- Δ).by(...)
val s2 = have((Γ, H) |- Δ) by Weakening(s1)
```

This is often needed right before `RightExists`, `LeftExists`, and `Cut`.

Useful: chained uses of `Restate` and `Weakening` can essentially always be merged into a single step

---

### `Tautology` in practice

`Tautology` is a workhorse for propositional reasoning and for chaining definitional lemmas.

```scala
val mem = SetTheoryStuff.membership.of(...)
val s = have(A, B |- C).by(Tautology.from(mem, otherLemma, previousStep))
```
`Tautology.from(...)` is sensitive to the *exact formula* it sees.
If you expected a lemma to match but it’s wrapped with a definition, `Tautology` may fail. 
Chained uses of `Tautology`, `Restate`, and `Weakening` can often be merged into a single `Tautology.from(...)` step, but if there are too many assumptions (let say more than 5) it can be less efficient to do so.

---



### Quantifiers: `InstantiateForall`, `Generalize`, `RightForall`

There are several ways to go back and forth between quantified statements and instances.

#### Instantiate a universal

```scala
val all = have(∀(x, P(x))).by(...)
val inst = have(P(t)).by(InstantiateForall(t)(all))
```

#### Build a universal from an arbitrary variable

Pattern:

1. Prove `P(x)` with `x` arbitrary.
2. Convert to `∀x P(x)`.

```scala
have(P(x)) subproof {
	// assume nothing about x beyond what you want
	...
}
thenHave(∀(x, P(x))).by(RightForall)
```

`Generalize` is also used in some files; it’s similar but depends on context.

---

### Schema instantiation with `.of(...)`

Many library results are *schema-like* theorems with named parameters (e.g. `A := ...`, `< := ...`, `x := ...`).
The `.of(...)` method instantiates such a theorem by providing concrete terms.

Typical shapes:

```scala
// A lemma with named set parameters
val inst = SomeLemma.of(A := A, < := R, x := t)

// A lemma with named predicate/function parameters often uses λ(...) lambdas
val inst2 = Quantifiers.existsEpsilon.of(x := x, P := λ(x, P(x)))
```

Then you can feed the instantiated statement into tactics:

```scala
val inst = Union.membership.of(x := A, y := B, z := t)
have(t ∈ (A ∪ B) <=> (t ∈ A) \/ (t ∈ B)).by(Tautology.from(inst))
```

**Things that weren’t obvious to me initially**

- The names in `.of(...)` must match the theorem’s parameter names (as defined in that lemma’s `of(...)` signature).
	If you guess the name wrong (e.g. `R := ...` vs `< := ...`), Scala will fail typechecking.

- Many definitions/lemmas use *non-obvious* parameter names (`<` for a relation, `X/Y` for sets, etc.).
	When in doubt, search for existing usages of the lemma and copy the instantiation pattern.

- `.of(...)` is not “proof”: it just produces the instantiated *statement*.
	You still need a tactic (`Tautology`, `Cut`, `InstantiateForall`, …) to actually use it.

**Recommendation**

- Prefer `.of(...)` with explicit named arguments over positional arguments; it’s much harder to mix up.
- When a proof fails due to a mismatch, inspect the instantiated statement (bind it to a `val inst = ...`) and compare it to your goal sequent.
- If the parameter/variable of the theorem is not in you namespace, you can always create a `val` for it first:

```scala
private val rareVariable = variable[Set]
val inst = SomeLemma.of(rareVariable := ...)
```

---

### Existentials: `RightExists`, `LeftExists`, and the safe pattern

#### Right ∃ (introduce)

To prove `Γ |- ∃(x, P(x))`, prove `Γ |- P(t)` then:

```scala
thenHave(Γ |- ∃(x, P(x))).by(RightExists)
```

The witness term is usually inferred from the shape of the previous step.

#### Left ∃ (eliminate)

To use `Γ, ∃(x, P(x)) |- Q`, prove `Γ, P(x) |- Q` with `x` fresh (or at least not constrained), then:

```scala
thenHave((Γ, ∃(x, P(x))) |- Q).by(LeftExists)
```

---

### `Cut`: powerful, but easy to mis-shape

`Cut(A, B)` roughly composes two proofs:

- one proving `Γ |- C`
- one using `C` to prove `Γ, C |- Δ`

Common pitfall:

- The “using” premise is `(Γ, C) |- Δ`, but you have `C |- Δ` or `(Γ', C) |- Δ`.
- Fix: `Weakening` to add missing assumptions or simply use `Tautology` in place of `Cut` (but it's less efficient sometimes).

---

### Equality, rewriting, and congruence

Use `Congruence.from(eq, argEq)` when you have an equation involving a term and you want to substitute an equal argument.

```scala
val step1 = have(G(x) === RHS(seg1)).by(...)
val segEq = have(seg1 === seg2).by(...)
have(G(x) === RHS(seg2)).by(Congruence.from(step1, segEq))
```

---

## 5) Steps names in proof scripts


Inside a proof block, Lisa maintains proof steps. They can be refered to by assigning them to Scala identifiers:
```scala
val step1 = have(P).by(...)
val step2 = thenHave(Q).by(Restate(step1))
```
When a step is used only once and immediately, you can use `thenHave(...)` without naming it.
```scala
have(P).by(...)
val step2 = thenHave(Q).by(Restate)
```

In addition, Lisa maintains an implicit “current result”: `lastStep` refers to the most recently produced proof step.
This is very convenient especially for tactics taking multiple premises, but it’s also a common source of fragile scripts.

Assumptions also work as steps, so that they can be used explicitly:
```scala
val stepH = assume(H)
```

**Pitfalls (things I got wrong at first)**

- `lastStep` changes *after every* `have(...)`, `thenHave(...)`, and nested `subproof`.
	If you insert a debugging lemma in the middle, references like `fromLastStep(...)` can silently start pointing to a different step.

- In nested `subproof` blocks, `lastStep` refers to the last step *in that subproof*, not outside it.

- Using `Tautology.fromLastStep(...)` can be brittle when the target lemma expects a different left-context (missing hypotheses, different ordering).
	Prefer naming the exact step and using `Weakening`/`Restate` explicitly.

**Recommendation**

- Use `lastStep` for very local glue.
- When a step is logically important (a key lemma, a cut formula, a quantifier instantiation), bind it to a `val` and refer to it by name.

---

## 6) Debug workflow that works

1. Run the proof entrypoint (often `sbt -client -no-colors "runMain ..."`).
2. Fix the *first* failing step (don’t guess downstream).

Practical debugging technique:

- Temporarily assign intermediate sequents to `val` names and re-run; the printed failure often references a subproof/step index that becomes easier to locate.

---

## 7) Lisa's logical system

### Lisa definitions
- There are different ways to define things in Lisa:
  - `def` for simple definitions that can be expanded inline.
  - `val` for constants or values that do not change.
  - `val myConstant = DEF(...)` for true definitions that are added to the Lisa environment, with a justification available to substitute them. 
  - `addSymbol(...)` for symbols that are not defined but added to the Lisa environment.

### Formula equivalence in Lisa
“Equivalent” formulas are often but not always interchangeable

I initially assumed tactics would accept formulas up to alpha-renaming / definitional equality / associativity of `∧`.
In practice, most formulas equivalent by Restate are interchangeable, but some tactics match syntactically (or nearly so).

Fix:

- Make equivalences explicit: `Restate`, or prove the exact `(<=>)` you need and then `Congruence`.



## 8) Style guide for Lisa files

In Lisa, we give great significance to the presentation and syntax of files. It should always be as readable and natural as possible. Consider the following possibilities and conventions:

- Lisa supports Unicode characters. Use them whenever possible to improve readability. For instance, use `ℕ` for natural numbers, `∈` for set membership, `∀` for universal quantification, etc.
- However, avoid using Unicode characters that can be represented using a conventional ASCII representation, unless it significantly improves readability. For example, prefer `->` over `→`, and similarly use `|-` instead of `⊢`, `\/` instead of `∨`, etc.
- Use infix notation for operations whenever possible. For example, use `a + b` instead of `add(a, b)`, and `a * b` instead of `mul(a, b)`.
- Scala offers many ways to define custom syntax, use them when necessary but keep the syntax's implementation as simple as possible.
- Theorems should be named in a way that reflects their content and purpose. Use descriptive names that make it easy to understand what the theorem is about at a glance.
- Add Scala doc over definitions and theorems to explain their purpose and usage.


## Making proofs shorter, cleaner, and more readable

This is a grab-bag of “high leverage” refactors that consistently made long LISA scripts smaller and less brittle.

### Avoid subproofs with single steps
If a `subproof { ... }` contains only one `have(...)` step, it should be inlined.
Example:

```scala
have(goal) subproof {
    assume(H)
    have(thesis).by(Tautology.from(stepA, stepB))
}
```
should be replaced by

```scala
have(goal).by(Tautology.from(stepA, stepB))
```
More generally, subproofs with too few steps (less than 4, unless they play a clear division role in the proof) should be inlined

### Factor out steps shared between subproofs
If a step is proven twice in different subproofs, factor it out of the subproofs.
Example
```scala
val step1 = have(goal1) subproof {
    val s = have(statement).by(...)
    ...
}
val step2 = have(goal2) subproof {
    val s = have(statement).by(...)
    ...
}
```
Can be replaced by
```scala
val s = have(statement).by(...)
val step1 = have(goal1) subproof {
    ...
}
val step2 = have(goal2) subproof {
    ...
}
``` 

### Name long formulas early and reuse them

When the *same* long formula appears in multiple places (especially inside `∃`, `∃!`, bounded `∀`, or inside `λ(G, ...)`), bind it once:

```scala
val Pm = (m ∈ A2) /\ functionOn(G)(initSeg(m)) /\ ∀(a ∈ initSeg(m), ...)
val exUnique = have(∃!(G, Pm)).by(...)
val ex = have(∃(G, Pm)).by(Tautology.from(exUnique, Quantifiers.existsOneImpliesExists.of(P := λ(G, Pm))))
```

### Factor “membership characterizations” into reusable lemmas

If you repeatedly need to unfold the same set/relation definition (e.g. successor set membership, union/intersection membership, relation constructors), prove the characterization once and reuse it:

```scala
val A2mem = have(z ∈ (A ∪ {m}) <=> (z ∈ A) \/ (z === m)).by(Tautology.from(...))
val R2mem = have((x, y) ∈ R2 <=> (...)).by(Tautology.from(...))
```



### Prefer library lemmas over re-proving basics

Before writing a `subproof` for a standard fact, search the library: many 10–30 line derivations already exist.

Examples that commonly replace manual work:

```scala
// Instead of a manual ⊆ proof for A ⊆ A ∪ {m}
val A2 = A ∪ singleton(m)
val ASubA2 = have(A ⊆ A2).by(Tautology.from(Union.leftSubset.of(x := A, y := singleton(m))))

// Similarly, {m} ⊆ A ∪ {m}
val mSubA2 = have(singleton(m) ⊆ A2).by(Tautology.from(Union.rightSubset.of(x := A, y := singleton(m))))
```

### Use “applied” theorems to avoid quantifier plumbing

Unfolding `transitive.definition` / `total.definition` / `irreflexive.definition` and then rebuilding `∀`-layers is a major source of line count.

Prefer the quantifier-free “applied” lemmas when available:

```scala
// Instead of: unfold irreflexive.definition; instantiate; restate
val notxx = have(¬(x R x)).by(Tautology.from(
	Relations.BasicTheorems.appliedIrreflexivity.of(R := R, X := A, x := x),
	irreflRA,
	xInA
))
```

### Collapse “glue steps” when safe

Many local chains of `Restate`/`Weakening`/`Tautology` can be merged into one `Tautology.from(...)` (or one `Tableau`) step.

Heuristic:

- If the steps are purely propositional or definitional, try merging.
- If you need multiple quantifier reshapes, `Tableau` can replace several `InstantiateForall` + `Restate` hops (Use sparsingly! `Tableaux is super inefficient`!)
- If `Tautology.from(...)` starts getting slow or fragile with many premises, split again.


### Don’t overuse `Tableau`

- Avoid replacing structured derivations with `Tableau` “because it’s shorter”.
	- `Tableau` can be *very* slow, and it can fail even when a human sees the propositional step is obvious.
	- In practice, `Tableau` is best kept for: reshaping bounded-quantifier encodings (`∀(x ∈ A, ...)`), or very small first-order glue.
- Especially avoid using `Tableau` for purely propositional steps.

### Don’t compress everything into one-liners

- Collapsing multi-line `Tautology.from(...)` into a single line is a line-count win, but doing it everywhere makes the proof harder to read and harder to debug.
- Rule of thumb: keep one-liners for “obvious glue”; keep multi-line blocks when they mark a conceptual boundary (e.g., “compute membership”, “use minimality”, “extract contradiction”).

### Don’t merge too many premises into one `Tautology.from(...)`

- There’s a sweet spot: a few premises is fast and robust; “kitchen sink” `Tautology.from(step1, ..., step12)` can become slow or fail to match.
- If you see timeouts/slowdowns, split the reasoning into 2–3 `Tautology.from(...)` steps with named intermediates.


## Prefer `Extensionality` for set equalities

If you already have a membership equivalence, close the goal directly:

```scala
have(z ∈ S <=> z ∈ T).by(...)
thenHave(S === T).by(Extensionality)
```

## Be disciplined with `lastStep`

`lastStep` is great for very local glue, but it makes later refactors fragile.

Patterns that helped:

- Bind important steps to a `val`.
- Avoid nesting proof-producing calls inside other tactic arguments.
- Don't use `val step = lastStep`; instead name the step or assumption directly when creating it.


### Keep `lastStep` local

- Use `lastStep` only for very short glue.
- Bind key steps (cut formulas, instantiated ∀, membership characterizations) to `val`s.
- Avoid `Tautology.fromLastStep(...)` unless the dependency is truly adjacent and stable.

### Use ` of (...)` with explicit names

- Prefer `SomeLemma.of(A := ..., < := ..., x := ...)` with named parameters.
- If you guess a parameter name wrong, Scala typechecking will fail; copy patterns from existing usages.

### Epsilon terms: always pair with existence

- When introducing `ε(x, P(x))`, also keep a proof of `∃x P(x)` around, then derive `P(ε(x,P(x)))` via `Quantifiers.existsEpsilon`.

### Replay workflow for proof compression

- Make a small number of changes.
- Replay immediately (e.g. `sbt --client -no-colors 'runMain ...'`).
- Only then proceed to the next refactor.
