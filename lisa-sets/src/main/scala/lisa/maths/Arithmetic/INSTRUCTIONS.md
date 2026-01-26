In this project, we develop arithmetic in the Lisa proof assistant, based on set theory.

## Scope (hard constraint)
- Only edit files under: `lisa-sets/src/main/scala/lisa/maths/Arithmetic/`
- Only use the namespace/package prefix: `lisa.maths.Arithmetic` (and subpackages)
- Every other folder of the project is off limits and must be left untouched.

We are using the library of Isabelle/HOL as a reference for our arithmetic development. The Isabelle/HOL library is located at: `IsabelleHOL/`.
We are using the library of Isabelle/HOL as a reference for our arithmetic development. The Isabelle/HOL library is located at: [IsabelleHOL/].

Reference policy:
- Use Isabelle/FOL for definition of arithmetic and the basic 'API'.
- Afterward Isabelle/HOL for lemma selection and overall structure.
- Do not copy/paste Isabelle code or comments verbatim.

## Goals
- The first step is to prove all the basic properties and helper lemmas of arithmetic: simple properties that we will need later. Look at the Isabelle/HOL library for reference, and add only useful theorems. These theorems should be named and organized properly, following the conventions in the [LISAHELP.md] file, to maximize future usability and searchability.


- The second step is to prove as many complex theorems about arithmetic as possible, proving intermediate lemmas. For this step, establish a list of theorems you want to prove, and discuss it with the project maintainer before starting the proofs. Write those "ideal goal theorems" in the [GOALS.md] file. Only consider theorems that can reasonably be proven with only the basic properties of arithmetic. Again, refer to the Isabelle/HOL library for inspiration, and make the list as large as possible so that there is a good chance that at least some theorems will be proven. Then, make a plan of intermediate useful lemmas that will help prove those theorems, also in the [GOALS.md] file. Finally, start proving as much of those theorems and lemmas as possible. At this stage, focus on making deep progress, while going back to prove more basic lemmas if necessary. You should split your time on easy, medium and hard theorems, to ensure that you make progress on all fronts. Overall, be ambitious! We want to prove impressive theorems. 

Recommended file organization:
- Put the list of long-term targets and intermediate lemma plans in [GOALS.md].
- Put the 10 example theorems in a dedicated file (e.g. [Examples.scala]) so they stay easy to find and run.

## Progress tracking
- Document important milestones and progress in the [PROGRESS.md] file under this folder. This file should contain a list of important steps of this project that have already been achieved. Only do it for very important steps, so that future AI agent can pick up where you left off easily. Don't use this file for documentation. Important achievements worth documenting are:
    - Completion of the basic properties and helper lemmas of arithmetic (step 1).
    - Completion of a major theorems about arithmetic (step 2).
    - Implementation of major tactics relevant to arithmetic proofs.
  While you are completing these steps, you can document intermediate progress in this file as well (at most 5 intermediate steps per major step). This will help future AI agents to understand what has already been done and what remains to be done. 

## IMPORTANT NOTES
- Do not modify any file outside of the `Arithmetic` folder and namespace.
- You can use theorems from set theory as needed, especially to define natural numbers and their operations. Then, you will still need to use definitions and lemmas about functions and relations, but should avoid using lower-level set-theoretic.
- If there are theorems from set theory that are required for the development of arithmetic, do not modify set-theory files directly. Instead, add these theorems to the [Necessary.scala] file in the `Arithmetic` folder.
- You should verify that your development is correct by running the Lisa proof assistant on it.
	- Use `sbt run` to get an interactive list of runnable theory files.
	- Or use `sbt --client -no-colors "runMain <classPath>"` to run a specific theory without prompt.
	- Compiling is not sufficient to ensure correctness! You must run the theory files that contain theorems you added or modified to ensure that all proofs are correct.
- Follow the LISAHELP guide in the [LISAHELP.md] file to ensure that your development is consistent and readable.
- Making proofs cleaner, simpler or shorter is considered progress and is encouraged. Making the development more maintainable is also considered progress. Changing the structure of the development to make it more suitable for future work is also acceptable, as long as it concretely adds value in the form of shorter development for the same results, or if it is immediately useful for future steps.
- It is acceptable to complete the proof of a theorem by `sorry` temporarily if the proof is too difficult and you don't succeed to complete it. Using `sorry` is preferable to using `Axiom`.
	- Any theorem left with `sorry` must still be correct, and mostly taken from either the Isabelle/HOL or from your list of goals (write in comment the source of the theorem).
	- Do not leave `sorry` in the 10 example theorems file.
- Do not remove existing theorems or definitions unless they are incorrect or redundant. Be extremely conservative about removing progress, and before doing so, make sure that it is absolutely necessary. We do not want to lose any progress that has already been made. If you think about removing a large portion of the file (i.e. 3 or more basic theorems, a more complex theorem or a definition), discuss it with the project maintainer first.
- Look at the [HELP.md] file for additional guidance and useful references in the Lisa project and the Isabelle/HOL library.

## New Tactics
- Consider adding new Tactics that are relevant to arithmetic proofs if you find that existing tactics are insufficient. However, avoid overcomplicating the tactic system; only add tactics that provide significant value and are likely to be reused in multiple proofs. Possible such tactics could be:
    - A tactic for simplifying expressions involving natural number operations (e.g., addition, multiplication).
    - A tactic for handling inequalities and order relations on natural numbers.
    - A tactic for automating common induction patterns on natural numbers.
- If you implement such tactics, document them properly and provide examples of their usage in the [Examples.scala] file. Make sure their syntax is correct. Also write tests for them in the `tests/` folder (one new file per tactic).
- Tactics are valuable and is considered significant progress, as long as they are well-documented and tested, and provide significant value to the arithmetic development. Do not implement tactics that you cannot immediately use to prove theorems in this project.