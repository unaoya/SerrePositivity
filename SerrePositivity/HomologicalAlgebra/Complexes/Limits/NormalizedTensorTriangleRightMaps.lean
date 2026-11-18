module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleRightPrisms
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePinchedFace
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
lemma normalizedTensorTriangleMap_face12 :
    (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ▷
      nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleMap A X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, c⟩
  let τ := (SimplexCategory.δ (0 : Fin 3)).toOrderHom.comp
    (SSet.stdSimplex.objEquiv t).toOrderHom
  change _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex A X Y c τ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y).app
      (Opposite.op ⦋n⦌) (t, c)
  have ht : ∀ i, τ i = 2 ↔ t i ≠ 0 := by
    intro i
    change (0 : Fin 3).succAbove (t i) = 2 ↔ t i ≠ 0
    generalize t i = j
    fin_cases j <;> decide
  apply Eq.trans ?_ (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationPrism_app_triangle A X Y c t τ ht).symm
  apply _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex_eq_back
  intro i
  change (0 : Fin 3).succAbove (t i) ≠ 0
  exact Fin.succAbove_ne _ _

lemma normalizedTensorTriangleMap_face02 :
    (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ▷
      nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleMap A X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, c⟩
  let τ := (SimplexCategory.δ (1 : Fin 3)).toOrderHom.comp
    (SSet.stdSimplex.objEquiv t).toOrderHom
  change _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex A X Y c τ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y)).app (Opposite.op ⦋n⦌) (t, c)
  have ht : ∀ i, τ i = 2 ↔ t i ≠ 0 := by
    intro i
    change (1 : Fin 3).succAbove (t i) = 2 ↔ t i ≠ 0
    generalize t i = j
    fin_cases j <;> decide
  apply Eq.trans ?_ (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedPrism_app_triangle A X Y c t τ ht).symm
  apply _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex_eq_pinched
  intro i
  change (1 : Fin 3).succAbove (t i) ≠ 1
  exact Fin.succAbove_ne _ _

end SerrePositivity.ComplexLimits
