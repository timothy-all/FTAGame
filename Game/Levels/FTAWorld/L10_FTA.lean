-- import GameServer
import Game.Levels.FTAWorld.L09_FTA

World "FTAWorld"
Level 10
Title "Permutations of prime lists"

Introduction "
# **Level 10**
This one is also intuitively clear, but it'll take a bit of Lean wrangling to see it through.
### **⌨ Typesetting Tip**
In order to write subscripts like `l₁` use `l\\_1`.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
As stated:
```
perm_prime
  (P Q : List Z)
  (hP : P.prime)
  (h  : P ~ Q) :
  Q.prime
```
If two lists are permutations of each other and the first list is a list of primes, then the second list is a list of primes as well.
-/
TheoremDoc perm_prime as "FTA : perm_prime"

/-- If two lists are permutations of each other and the first list is a list of primes, then the second list is a list of primes as well.-/
Statement perm_prime
  (P Q : List Z)
  (hP : P.prime)
  (h  : P ~ Q) :
  Q.prime := by
  induction h
  exact hP
  intro p pmem
  cases pmem
  exact hP x (Mem.head l₁)
  obtain l₁_prime := prime_tail (x :: l₁) hP
  obtain l₂_prime := a_ih l₁_prime
  exact l₂_prime p a_1
  intro s hs
  cases hs
  obtain tail_prime := prime_tail (y :: x :: l) hP
  exact tail_prime x (Mem.head l)
  rcases a with left | right
  exact hP y (Mem.head (x :: l))
  obtain ttail_prime := prime_tail (x :: l) (prime_tail (y :: x :: l) hP)
  exact ttail_prime s a_1
  exact a_ih_1 (a_ih hP)

Conclusion "
"
