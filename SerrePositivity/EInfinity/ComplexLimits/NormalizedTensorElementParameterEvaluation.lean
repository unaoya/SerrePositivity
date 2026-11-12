module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversalEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementParameter

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementParameterMap_app {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorElementParameterMap A X Y).app (Opposite.op ⦋n⦌) c =
    ULift.up ((normalizedSimplexTensor A X).map
      (normalizedTensorElementTerminalParameter A X Y c) ≫
        (normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))) := rfl

lemma normalizedTensorHomPinchedSimplex_id_eval (n : ℕ)
    (g : (normalizedSimplexTensor A X).obj ⦋n⦌ ⟶ Y) :
    (normalizedTensorHomPinchedSimplex A X Y ⦋n⦌ g).app (Opposite.op ⦋n⦌)
      (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
    (normalizedTensorPinchedIso A X Y).hom.app (Opposite.op ⦋n⦌) (ULift.up g) := by
  change (normalizedTensorPinchedIso A X Y).hom.app (Opposite.op ⦋n⦌)
    (ULift.up (SSet.yonedaEquiv (normalizedTensorHomRepresentable A X Y ⦋n⦌ g))) = _
  rw [normalizedTensorHomRepresentable, Equiv.apply_symm_apply]

end SerrePositivity.EInfinity.ComplexLimits
