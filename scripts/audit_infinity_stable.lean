import SerrePositivity.InfinityCategories.Stable
import Lean.Util.CollectAxioms

/-! # 安定 ∞ 圏の全宣言の公理監査

概要：実装モジュールの全宣言と主要公開宣言の公理を監査する。
方針：生成補題も含めて依存公理を列挙し許可リストで検査する。
規約：propext・Classical.choice・Quot.sound のみ。
使われ方：対象ビルド後の `lake env lean scripts/audit_infinity_stable.lean`。
-/

#print axioms SerrePositivity.InfinityCategories.JoinCocone
#print axioms SerrePositivity.InfinityCategories.JoinCocone.vertex
#print axioms SerrePositivity.InfinityCategories.JoinCocone.vertex_eq
#print axioms SerrePositivity.InfinityCategories.IsColimitCone
#print axioms SerrePositivity.InfinityCategories.HasColimit
#print axioms SerrePositivity.InfinityCategories.isColimitCone_iff_trivialKanFibration
#print axioms SerrePositivity.InfinityCategories.colimitConeIso
#print axioms SerrePositivity.InfinityCategories.colimitVertexIso
#print axioms SerrePositivity.InfinityCategories.joinCoconeFamilyEquiv
#print axioms SerrePositivity.InfinityCategories.spanCoconeTriangleLeft
#print axioms SerrePositivity.InfinityCategories.spanCoconeTriangleRight
#print axioms SerrePositivity.InfinityCategories.spanCocone_gluing
#print axioms SerrePositivity.InfinityCategories.spanCocone_isPushout
#print axioms SerrePositivity.InfinityCategories.spanCoconeSquareIso
#print axioms SerrePositivity.InfinityCategories.spanCoconeSquareIso_left
#print axioms SerrePositivity.InfinityCategories.spanCoconeSquareIso_right
#print axioms SerrePositivity.InfinityCategories.squareBottomEdge
#print axioms SerrePositivity.InfinityCategories.squareLeftEdge
#print axioms SerrePositivity.InfinityCategories.spanSquareBoundary
#print axioms SerrePositivity.InfinityCategories.pushoutSpan
#print axioms SerrePositivity.InfinityCategories.pushoutCocone
#print axioms SerrePositivity.InfinityCategories.IsPushoutSquare
#print axioms SerrePositivity.InfinityCategories.joinStdSimplexIso_one_zero_inl
#print axioms SerrePositivity.InfinityCategories.spanSquareBoundary_bottomEdge
#print axioms SerrePositivity.InfinityCategories.spanSquareBoundary_leftEdge
#print axioms SerrePositivity.InfinityCategories.isPushoutSquare_iff_trivialKanFibration
#print axioms SerrePositivity.InfinityCategories.IsZeroVertex
#print axioms SerrePositivity.InfinityCategories.ZeroVertex
#print axioms SerrePositivity.InfinityCategories.HasZeroVertex
#print axioms SerrePositivity.InfinityCategories.ZeroVertex.isZero
#print axioms SerrePositivity.InfinityCategories.chosenZeroVertex
#print axioms SerrePositivity.InfinityCategories.zeroVertexIso
#print axioms SerrePositivity.InfinityCategories.squareVertex
#print axioms SerrePositivity.InfinityCategories.ZeroTriangle
#print axioms SerrePositivity.InfinityCategories.IsFiberSequence
#print axioms SerrePositivity.InfinityCategories.IsCofiberSequence
#print axioms SerrePositivity.InfinityCategories.FiberSquare
#print axioms SerrePositivity.InfinityCategories.CofiberSquare
#print axioms SerrePositivity.InfinityCategories.FiberSquare.fiber
#print axioms SerrePositivity.InfinityCategories.CofiberSquare.cofiber

#print axioms SerrePositivity.InfinityCategories.edgeSimplex_source
#print axioms SerrePositivity.InfinityCategories.edgeSimplex_target
#print axioms SerrePositivity.InfinityCategories.edgeCospan
#print axioms SerrePositivity.InfinityCategories.edgeCospan_left
#print axioms SerrePositivity.InfinityCategories.edgeCospan_right
#print axioms SerrePositivity.InfinityCategories.edgeSpan
#print axioms SerrePositivity.InfinityCategories.edgeSpan_left
#print axioms SerrePositivity.InfinityCategories.edgeSpan_right
#print axioms SerrePositivity.InfinityCategories.coneSquare
#print axioms SerrePositivity.InfinityCategories.coneSquare_cospan
#print axioms SerrePositivity.InfinityCategories.coneSquare_isPullback
#print axioms SerrePositivity.InfinityCategories.coconeSquare
#print axioms SerrePositivity.InfinityCategories.coconeSquare_span
#print axioms SerrePositivity.InfinityCategories.coconeSquare_isPushout
#print axioms SerrePositivity.InfinityCategories.coneSquare_right
#print axioms SerrePositivity.InfinityCategories.coneSquare_top
#print axioms SerrePositivity.InfinityCategories.coconeSquare_bottom
#print axioms SerrePositivity.InfinityCategories.coconeSquare_left
#print axioms SerrePositivity.InfinityCategories.squareTopEdge_source
#print axioms SerrePositivity.InfinityCategories.squareLeftEdge_target
#print axioms SerrePositivity.InfinityCategories.exists_fiberSquare_of_cospan_limits
#print axioms SerrePositivity.InfinityCategories.exists_cofiberSquare_of_span_colimits
#print axioms SerrePositivity.InfinityCategories.HasFiniteLimits
#print axioms SerrePositivity.InfinityCategories.HasFiniteColimits
#print axioms SerrePositivity.InfinityCategories.IsStable
#print axioms SerrePositivity.InfinityCategories.chosenFiberSquare
#print axioms SerrePositivity.InfinityCategories.chosenCofiberSquare
#print axioms SerrePositivity.InfinityCategories.IsStable.pushout_of_pullback
#print axioms SerrePositivity.InfinityCategories.IsStable.pullback_of_pushout
#print axioms SerrePositivity.InfinityCategories.isStable_of_finite_limits_colimits

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.InfinityCategories.Stable.Cocone,
    `SerrePositivity.InfinityCategories.Stable.PushoutShape,
    `SerrePositivity.InfinityCategories.Stable.Pointed,
    `SerrePositivity.InfinityCategories.Stable.FiniteShapes,
    `SerrePositivity.InfinityCategories.Stable.Definition]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Stable axiom audit passed: {count} declarations in {seen.size} modules."
