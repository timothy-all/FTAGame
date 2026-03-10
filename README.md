# The FTA Game

The object of this game, mathematically speaking, is prove the **F**undamental **T**heorem of **A**rithmetic over ℤ, the integers. But we'll also learn about L∃∀N.

### **What is Lean?**

Lean (stylized as L∃∀N) is a proof assistant and programming language -- this means that it helps to codify mathematical proofs. As we write proofs of our claims (or theorems) in Lean, a terminal will dynamically report our givens and goals. As goals get cleared, we'll stock an inventory of rigorous, *machine-verified* proofs of theorems that can be subsequently used to prove new goals.

In 2017, the mathematical community began the project of creating the Lean library `mathlib` with the goal formalizing (and therefore machine-verifying) as much pure mathematics as possible. This game does **not** import `mathlib` or any of its libraries. ***We start from scratch!*** Specifically, we define ℤ as an ordered Ring satisfying the well-ordering principle.

