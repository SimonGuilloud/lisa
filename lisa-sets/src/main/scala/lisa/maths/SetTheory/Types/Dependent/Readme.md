# Dependent types

[![Scala](https://img.shields.io/badge/scala-3.x-red.svg)](https://www.scala-lang.org/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)

This module implements a mechanized embedding of **Dependent Type Theory** (specifically dependent products and universes) into **First-Order Logic with ZFC axioms** within the [LISA Proof Assistant](https://github.com/lisa-proof-assistant/lisa).

Following the "types-as-sets" paradigm, this project aims to bridge the foundational gap between type-theoretic systems (like Lean 4 and Rocq) and set-theoretic foundations. It provides the necessary infrastructure to import mathematical libraries from dependent type theory into LISA's ZFC environment.

## 🚀 Key Features

### 1. Set-Theoretic Embedding of Types
* **Graph-Theoretic Functions**: Functions are modeled as functional graphs (sets of ordered pairs $\langle x, y \rangle$). Abstraction (`abs`) and Application (`app`) are defined using set-theoretic operations verified via $\beta$-reduction.
* **Dependent Products ($\Pi$-types)**: Modeled as generalized Cartesian products using restricted comprehension. A type $\Pi(x:T_1).T_2(x)$ is the set of functional graphs where inputs $x \in T_1$ map to outputs in $T_2(x).
* **A-FOL Integration**: Utilizes LISA's **A-FOL** (First-Order Logic with A-terms) to handle flexible variable binding and sort systems (`Ind` for individuals, `Prop` for propositions).

### 2. Grothendieck Universe Hierarchies
* **Tarski's Axiom**: Standard ZFC is extended with Tarski's Axiom to ensure the existence of Grothendieck universes, overcoming ZFC's inability to model a "set of all sets".
* **`universeOf` Operator**: Implements a `universeOf(x)` operator using Hilbert's $\epsilon$-operator, mapping any set/type to a universe containing it. This supports cumulative hierarchies ($Type_i : Type_{i+1}$).

### 3. Automated Proof Generation
* **Bidirectional Type Checking**: A `Typecheck.prove` tactic automates the derivation of ZFC proofs. Unlike standard checkers that return a boolean, this tactic produces a verifiable LISA proof object.
* **Three-Mode Checking**:
    * **Check Mode**: Verifies terms against expected types.
    * **Infer Mode**: Computes the type of a term (e.g., for applications $e_1(e_2)$).
    * **Subset Mode**: Handles subtyping relations, specifically supporting **domain invariance** and **codomain covariance** for $\Pi$-types.
