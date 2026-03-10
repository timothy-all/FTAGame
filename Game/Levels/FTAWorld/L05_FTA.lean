-- import GameServer
import Game.Levels.FTAWorld.L04_FTA

World "FTAWorld"
Level 5
Title "Primes dividing list products"

Introduction "
# **Level 5**
This exercise is an important generalization of `prime_dvd_mul` ... and we'll use **induction**.
### 🤔 Wait a minute...
***I thought we were WOP-folk around here!?*** Yes, this is still largely the case. But there are instances (like in this level) where we need to argue inductively on the **number of items in a list** -- a quantity codified with ℕ, the natural numbers. We could unify our construction of ℤ with that of ℕ and eventually use WOP for such arguments, but this would divert too much of our attention from our main goal.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor and an **inductive hypothesis** is added for each **recursive** argument to the constructor.
-/
TacticDoc induction

/--
As stated:
```
prime_dvd_prod
  (p : Z)
  (l : List Z)
  (hl : List.prime l)
  (hp : Prime p)
  (hd : p ∣ List.prod l) :
  p ∈ l
```
If $p ∈ ℤ$ is a prime that divides the product of all members of a list of primes, then $p$ is a member of that list.
-/
TheoremDoc prime_dvd_prod as "FTA : prime_dvd_prod"

/-- If $p ∈ ℤ$ is a prime that divides the product of all members of a list of primes, then $p$ is a member of that list. -/
Statement prime_dvd_prod
  (p : Z)
  (l : List Z)
  (hl : List.prime l)
  (hp : Prime p)
  (hd : p ∣ l.prod) :
  p ∈ l := by
  Hint "### ❯ The `induction` tactic
  We'll use induction here. 🔍 Check out the entry for the tactic `induction` in the **Tactics** tab. Specifically, we should induct on the number of elements in `{l}`. 👉 To do so, try
  ```
  induction l
  ```
  This ought to split the main goal into cases...
  "
  induction l
  Hint "... the first of which is the **base** case. In the present case, this means we assume that `l` is the empty list. In other words, our goal is `⊢ p ∈ []` -- this is `False`. So we should look for a contradiction."
  simp
  rw[List.prod] at hd
  exact prime_dvd_one p hp hd
  Hint "We're now in the **inductive step**. In the present case, this means we assume that `l` is of the form `(head :: tail)`. What's more, we have the **inductive hypothesis**
  ```
  tail_ih : tail.prime → p ∣ tail.prod → p ∈ tail
  ```
  "
  rw[List.prod] at hd
  obtain left | right := prime_dvd_mul head (tail.prod) p hp hd
  obtain eq := prime_dvd_prime p head hp (hl head (Mem.head tail)) left
  rw[eq]
  exact Mem.head tail
  obtain pt := tail_ih (prime_tail (head :: tail) hl) right
  simp[pt]

Conclusion "
"

NewTactic induction
