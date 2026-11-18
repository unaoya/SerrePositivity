module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementUniversalEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementParameter

/-!
概要：元の大域パラメータの全単体値と、終端の実 frame 射による評価を照合する。
方針：同じ終端パラメータを元の cosimplicial Hom と代表可能単体で評価する。
規約：元の大域射自身の全次数の式を保持する。
使われ方：大域 prism の評価端点と元の pinched 評価族の厳密な一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementParameterMap_app {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementParameterMap A X Y).app (Opposite.op ⦋n⦌) c =
    ULift.up ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementTerminalParameter A X Y c) ≫
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))) := rfl

lemma normalizedTensorHomPinchedSimplex_id_eval (n : ℕ)
    (g : (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj ⦋n⦌ ⟶ Y) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex A X Y ⦋n⦌ g).app (Opposite.op ⦋n⦌)
      (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y).hom.app (Opposite.op ⦋n⦌) (ULift.up g) := by
  change (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y).hom.app (Opposite.op ⦋n⦌)
    (ULift.up (SSet.yonedaEquiv (_root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable A X Y ⦋n⦌ g))) = _
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorHomRepresentable, Equiv.apply_symm_apply]

end SerrePositivity.ComplexLimits
