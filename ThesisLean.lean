import ThesisLean.Basic
import ThesisLean.ChallengeDefs
import ThesisLean.SolutionBridge
import ThesisLean.Correctness
import ThesisLean.Formal_gen001c01_3939115c
import ThesisLean.Formal_gen003c01_eea71821
import ThesisLean.Exec
import ThesisLean.ExecBridge
import ThesisLean.BridgeSteps
import ThesisLean.CardBridge
import ThesisLean.McsInvariant
import ThesisLean.BridgePartsA
import ThesisLean.BridgePartsB
import ThesisLean.BridgePartsC
import ThesisLean.BridgeAssembly
import ThesisLean.ExecFlip
-- All modules above are the Palomar submission artifact. They are imported
-- here so CI (lean-action) builds all of them and the leanchecker step can
-- re-verify every module (the glob in lean_action_ci.yml picks up each
-- built .olean).