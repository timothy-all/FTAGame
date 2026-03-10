import GameServer
import Game.Levels.TestWorld
import Game.Levels.OrderWorld
import Game.Levels.absWorld
import Game.Levels.WOPWorld
import Game.Levels.DivisionWorld
import Game.Levels.PrimeWorld
import Game.Levels.GCDWorld
import Game.Levels.FTAWorld
import Game.Metadata

-- Here's what we'll put on the title screen
Title "The FTA Game"
Introduction
"
# **The FTA Game**

Welcome to **The FTA Game**. The object of this game, mathematically speaking, is prove the **F**undamental **T**heorem of **A**rithmetic over ℤ, the integers. But we'll also learn about L∃∀N.

### **What is Lean?**

Lean (stylized as L∃∀N) is a proof assistant and programming language -- this means that it helps to codify mathematical proofs. As we write proofs of our claims (or theorems) in Lean, a terminal will dynamically report our givens and goals. As goals get cleared, we'll stock an inventory of rigorous, *machine-verified* proofs of theorems that can be subsequently used to prove new goals.

In 2017, the mathematical community began the project of creating the Lean library `mathlib` with the goal formalizing (and therefore machine-verifying) as much pure mathematics as possible. This game does **not** import `mathlib` or any of its libraries. ***We start from scratch!*** Specifically, we define ℤ as an ordered Ring satisfying the well-ordering principle.

### **How to play?**

The world map is in the center pane. Individual world-levels are the pearls encircling the worlds. Once you've cleared a level, you can move onto the next. The same thing is true with worlds. You can replay any level by navigating to it from the world map. **Start** with **Ring Axiom World**.
"

Info "
This game was made by me.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "FTA Game"
CaptionLong "This game has you prove the Fundamental Theorem of Arithmetic ... from scratch!"
-- Prerequisites "" -- add this if your game depends on other games
CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/

--Dependency RingWorld → OrderWorld → WOPWorld → PrimeWorld → GCDWorld
--Dependency DivisionWorld → GCDWorld

MakeGame
