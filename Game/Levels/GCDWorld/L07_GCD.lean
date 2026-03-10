-- import GameServer
import Game.Levels.GCDWorld.L06_GCD

World "GCDWorld"
Level 7
Title ""

Introduction "
# **Level 7**
This one takes a bit of patience.
"

variable {Z : Type} [RRZ : RossRing Z]


/--
As stated:
```
div_alg_mem_Bez
  (a b m q r: Z)
  (hm : ∃ x y : Z, a * x + b * y = m)
  (eq : a = m * q + r) :
  ∃ x y : Z , a * x + b * y = r
```
Let $a,b,m,q,r ∈ ℤ$. If $m$ is a $ℤ$-linear combination of $a$ and $b$ and $a = qm + r$, then $r$ is also a $ℤ$-linear combination of $a$ and $b$.
-/
TheoremDoc div_alg_mem_Bez as "GCD : div_alg_mem_Bez"

/-- Let $a,b,m,q,r ∈ ℤ$. If $m$ is a $ℤ$-linear combination of $a$ and $b$ and $a = qm + r$ where $r$ is positive, then $r$ is a positive $ℤ$-linear combination of $a$ and $b$.-/
Statement div_alg_mem_Bez
  (a b m q r: Z)
  (hmB : m ∈ Bez a b)
  (eq : a = m * q + r)
  (hr : 0 < r) :
  r ∈ Bez a b:= by
  refine ⟨hr,?_⟩
  obtain ⟨u,v,meq⟩ := hmB.right
  use (1 + -u * q)
  use -v * q
  rw[mul_add]
  simp[← neg_mul_left,← neg_mul_right,← mul_assoc]
  rw[mul_comm _ q, mul_comm _ q,add_assoc,neg_add,← mul_add,meq]
  rw[eq,add_comm _ r,add_assoc,mul_comm]
  simp


Conclusion "
"
