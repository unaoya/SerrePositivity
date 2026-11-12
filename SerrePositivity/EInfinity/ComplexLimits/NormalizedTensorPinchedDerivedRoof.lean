module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleFamilyComposition
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeDerivedRoof
/-! 概要：元の全 pinched 族を同じ導来 roof に同定する。
方針：全関手圏内の評価三角形と元の augmentation 逆を同じ関手で送る。
規約：全 K と端点輸送を保持。使われ方：標準単位比較自身の全高次比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
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
    Arrow.mk ((hoFunctor.map ((ihom (nerve (normalizedTensorElementIndex A X Y))).map
      (complexSemifreeResolutionInfinity A))).toFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (normalizedTensorElementPinchedMap A X Y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)))) =
      Arrow.mk (normalizedTensorElementDerivedRoof A X Y) := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let F := complexSemifreeResolutionInfinity A
  let T := (hoFunctor.map ((ihom K).map F)).toFunctor
  let e := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (normalizedTensorEvaluationHomotopy A X Y))
  have hc : Arrow.mk (T.map (normalizedTensorConeFamilyHom A X Y)) =
      Arrow.mk (normalizedTensorElementDerivedAugmentationIso A X Y).inv := by
    exact (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom
      (normalizedTensorConeHomotopy A X Y) F)).symm.trans
        (normalizedTensorConePostDerived_inverse_arrow A X Y)
  have he : Arrow.mk (T.map e) = Arrow.mk (normalizedTensorElementDerivedEvaluation A X Y) := by
    apply Eq.trans (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom
      (normalizedTensorEvaluationHomotopy A X Y) F)).symm
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (normalizedTensorEvaluationHomotopy A X Y) F)
      (complexOrdinaryDerivedNatTransHomotopy A (normalizedTensorElementEvaluation A X Y))
    exact Category.assoc _ _ _
  have ht := congrArg T.map (normalizedTensorTriangleFamily_comp A X Y)
  rw [CategoryTheory.Functor.map_comp] at ht
  exact (congrArg Arrow.mk ht.symm).trans (arrow_comp_of_eq _ _ _ _ hc he)

end SerrePositivity.EInfinity.ComplexLimits
