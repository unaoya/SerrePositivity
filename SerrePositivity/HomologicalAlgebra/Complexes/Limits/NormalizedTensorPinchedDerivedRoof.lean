module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleFamilyComposition
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeDerivedRoof
/-! 概要：元の全 pinched 族を同じ導来 roof に同定する。
方針：全関手圏内の評価三角形と元の augmentation 逆を同じ関手で送る。
規約：全 K と端点輸送を保持。使われ方：標準単位比較自身の全高次比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
private lemma arrow_comp_of_eq {C : Type*} [Category* C]
    {x y z x' y' z' : C} (f : x ⟶ y) (g : y ⟶ z) (f' : x' ⟶ y') (g' : y' ⟶ z')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff f f').mp hf
  obtain ⟨_, hz, hg⟩ := (Arrow.mk_eq_mk_iff g g').mp hg
  cases hx
  cases hy
  cases hz
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  cases hf
  cases hg
  rfl

variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorPinchedFamilyPostDerived_arrow :
    Arrow.mk ((hoFunctor.map ((ihom (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))).map
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A))).toFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)))) =
      Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A X Y) := by
  let K := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)
  let F := _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A
  let T := (hoFunctor.map ((ihom K).map F)).toFunctor
  let e := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationHomotopy A X Y))
  have hc : Arrow.mk (T.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeFamilyHom A X Y)) =
      Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).inv := by
    exact (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeHomotopy A X Y) F)).symm.trans
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePostDerived_inverse_arrow A X Y)
  have he : Arrow.mk (T.map e) = Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedEvaluation A X Y) := by
    apply Eq.trans (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationHomotopy A X Y) F)).symm
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationHomotopy A X Y) F)
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y))
    exact Category.assoc _ _ _
  have ht := congrArg T.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFamily_comp A X Y)
  rw [CategoryTheory.Functor.map_comp] at ht
  exact (congrArg Arrow.mk ht.symm).trans (_root_.SerrePositivity.ComplexLimits.arrow_comp_of_eq _ _ _ _ hc he)

end SerrePositivity.ComplexLimits
