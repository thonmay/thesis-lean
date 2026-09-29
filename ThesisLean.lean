module

public import ThesisLean.Basic
public import ThesisLean.ChallengeDefs
public import ThesisLean.SolutionBridge
public import ThesisLean.Correctness
public import ThesisLean.ExecUpdate
public import ThesisLean.Stability
public import ThesisLean.Formal_gen001c01_3939115c
public import ThesisLean.Formal_gen003c01_eea71821
public import ThesisLean.Exec
public import ThesisLean.ExecBridge
public import ThesisLean.BridgeSteps
public import ThesisLean.CardBridge
public import ThesisLean.McsInvariant
public import ThesisLean.BridgePartsA
public import ThesisLean.BridgePartsB
public import ThesisLean.BridgePartsC
public import ThesisLean.BridgeAssembly
public import ThesisLean.ExecFlip

set_option backward.proofsInPublic true
@[expose] public section
-- All modules above are the Palomar submission artifact. They are imported
-- here so CI (lean-action) builds all of them and the leanchecker step can
-- re-verify every module (the glob in lean_action_ci.yml picks up each
-- built .olean).