module

import all ThesisLean.Basic
import all ThesisLean.ChallengeDefs
import all ThesisLean.SolutionBridge
import all ThesisLean.Correctness
import all ThesisLean.ExecUpdate
import all ThesisLean.Stability
import all ThesisLean.Formal_gen001c01_3939115c
import all ThesisLean.Formal_gen003c01_eea71821
import all ThesisLean.Exec
import all ThesisLean.ExecBridge
import all ThesisLean.BridgeSteps
import all ThesisLean.CardBridge
import all ThesisLean.McsInvariant
import all ThesisLean.BridgePartsA
import all ThesisLean.BridgePartsB
import all ThesisLean.BridgePartsC
import all ThesisLean.BridgeAssembly
import all ThesisLean.ExecFlip

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
-- All modules above are the Palomar submission artifact. They are imported
-- here so CI (lean-action) builds all of them and the leanchecker step can
-- re-verify every module (the glob in lean_action_ci.yml picks up each
-- built .olean).