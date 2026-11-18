module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleOrdinaryFaces
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConePrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftPrismEvaluation
/-! 概要：大域三角形の各面を元の円柱と区間族へ同定する。
方針：既存の左右 prism 評価式で全単体を同じ切断へ戻す。
規約：全 K を保持。使われ方：元の評価三角形の全関手圏での合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorConePrism_app_triangle {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (τ : Fin (n + 1) →o Fin 3)
    (ht : ∀ i, τ i = 0 ↔ t i = 0) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePrism A X Y).app (Opposite.op ⦋n⦌) (t, c) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ := by
  have hc : SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin A X Y) = _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c := by
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin_restrict_simplex]
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ _) = _
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  have ht' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut (SSet.stdSimplex.objEquiv t).toOrderHom =
      _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ := by
    apply DFunLike.ext
    intro i
    change (if t i = 0 then 0 else i.succ) = (if τ i = 0 then 0 else i.succ)
    by_cases hi : τ i = 0
    · simp [hi, (ht i).mp hi]
    · simp [hi, mt (ht i).mpr hi]
  change (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin A X Y).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism _).app (Opposite.op ⦋n⦌) (t, c)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftMappingSpacePrism_evaluate, hc, ht']
  rfl

lemma normalizedTensorTriangleMap_face01 :
    (SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ▷
      nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleMap A X Y =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConePrism A X Y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, c⟩
  let τ := (SimplexCategory.δ (2 : Fin 3)).toOrderHom.comp
    (SSet.stdSimplex.objEquiv t).toOrderHom
  change _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex A X Y c τ =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePrism A X Y).app (Opposite.op ⦋n⦌) (t, c)
  have ht : ∀ i, τ i = 0 ↔ t i = 0 := by
    intro i
    change (2 : Fin 3).succAbove (t i) = 0 ↔ t i = 0
    generalize t i = j
    fin_cases j <;> decide
  apply Eq.trans ?_ (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePrism_app_triangle A X Y c t τ ht).symm
  apply _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex_eq_front
  intro i
  change (2 : Fin 3).succAbove (t i) ≠ 2
  exact Fin.succAbove_ne _ _

end SerrePositivity.ComplexLimits
