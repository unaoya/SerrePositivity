module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleRightPrisms
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePinchedFace
/-! 概要：大域三角形の各面を元の円柱と区間族へ同定する。
方針：既存の左右 prism 評価式で全単体を同じ切断へ戻す。
規約：全 K を保持。使われ方：元の評価三角形の全関手圏での合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorTriangleMap_face12 :
    (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ▷
      nerve (normalizedTensorElementIndex A X Y)) ≫ normalizedTensorTriangleMap A X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ normalizedTensorElementEvaluationJoin A X Y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, c⟩
  let τ := (SimplexCategory.δ (0 : Fin 3)).toOrderHom.comp
    (SSet.stdSimplex.objEquiv t).toOrderHom
  change normalizedTensorTriangleSimplex A X Y c τ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ normalizedTensorElementEvaluationJoin A X Y).app
      (Opposite.op ⦋n⦌) (t, c)
  have ht : ∀ i, τ i = 2 ↔ t i ≠ 0 := by
    intro i
    change (0 : Fin 3).succAbove (t i) = 2 ↔ t i ≠ 0
    generalize t i = j
    fin_cases j <;> decide
  apply Eq.trans ?_ (normalizedTensorEvaluationPrism_app_triangle A X Y c t τ ht).symm
  apply normalizedTensorTriangleSimplex_eq_back
  intro i
  change (0 : Fin 3).succAbove (t i) ≠ 0
  exact Fin.succAbove_ne _ _

lemma normalizedTensorTriangleMap_face02 :
    (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ▷
      nerve (normalizedTensorElementIndex A X Y)) ≫ normalizedTensorTriangleMap A X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (normalizedTensorElementPinchedMap A X Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, c⟩
  let τ := (SimplexCategory.δ (1 : Fin 3)).toOrderHom.comp
    (SSet.stdSimplex.objEquiv t).toOrderHom
  change normalizedTensorTriangleSimplex A X Y c τ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry
      (normalizedTensorElementPinchedMap A X Y)).app (Opposite.op ⦋n⦌) (t, c)
  have ht : ∀ i, τ i = 2 ↔ t i ≠ 0 := by
    intro i
    change (1 : Fin 3).succAbove (t i) = 2 ↔ t i ≠ 0
    generalize t i = j
    fin_cases j <;> decide
  apply Eq.trans ?_ (normalizedTensorPinchedPrism_app_triangle A X Y c t τ ht).symm
  apply normalizedTensorTriangleSimplex_eq_pinched
  intro i
  change (1 : Fin 3).succAbove (t i) ≠ 1
  exact Fin.succAbove_ne _ _

end SerrePositivity.EInfinity.ComplexLimits
