--import GameServer.Graph

import Game.Levels.TestWorld.L16_test
import Game.Levels.TestWorld.L15_test
import Game.Levels.TestWorld.L14_test
import Game.Levels.TestWorld.L13_test
import Game.Levels.TestWorld.L12_test
import Game.Levels.TestWorld.L11_test
import Game.Levels.TestWorld.L10_test
import Game.Levels.TestWorld.L09_test
import Game.Levels.TestWorld.L08_test
import Game.Levels.TestWorld.L07_test
import Game.Levels.TestWorld.L06_test
import Game.Levels.TestWorld.L05_test
import Game.Levels.TestWorld.L04_test
import Game.Levels.TestWorld.L03_test
import Game.Levels.TestWorld.L02_test
import Game.Levels.TestWorld.L01_test

World "RingWorld"
Title "Ring World"


Introduction
"
# **Welcome to Ring World!**
In this world we'll familiarize ourselves with Lean by proving some well-known facts about (Ring) arithmetic. First, let's explore the interface a bit.
### **Tactics**
🔍 Check out the **Tactics** tab in the right-pane. Tactics are used to prove theorems in Lean. Think of them as codified *proof strategies*. We'll learn more about tactics as we move forward. Most of these are 🔒*locked*🔒 at this time, they will unlock as we need them going forward.
### **⌨ Typesetting**
Lean uses the standard logical notations (typesetting in parantheses):
* `∀` : for all (`\\forall`)
* `∃` : there exists (`\\exists`)
* `p → q` : if `p`, then `q` (`\\to`)
* `p ↔ q` : `p` if and only if `q` (`\\iff`)
* `p ∧ q` : `p` and `q` (`\\wedge`)
* `p ∨ q` : `p` or `q` (`\\vee`)
* `¬` : *not*/negation (`\\neg`)
"

Image "images/cover.png"
