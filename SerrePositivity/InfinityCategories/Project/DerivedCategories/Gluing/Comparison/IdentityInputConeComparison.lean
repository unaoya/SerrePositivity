module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.IdentityNativeConeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.IdentityInputDiagonalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityLaxArrowBaseCofiber
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityValueEquivalences
/-!
概要：恒等二脚の同じ元実 cone 差と選択 lax 差を、指定固定入力上で全比較する。
方針：native の全 cone 比較を全 ν 自然性・全像包含評価と指定往復則で運ぶ。
規約：元中央同値と元差終域同値を保持。使われ方：恒等比較入力の cone 欄。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits SSet DifferentialGraded KST.SConstruction
open _root_.SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => DGOdotMilnorIdentityBase R d
local notation "L" => DGOdotMilnorIdentityGluing R d
local notation "D" => DGOdotMilnorIdentityDifference R d
local notation "I" => DGFunctor.id (A := R) C
local instance dgGluingIdentityInputConeBase_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C := dgOdotMilnorIdentityBase_pretriangulated R d
local instance dgGluingIdentityInputConeSource_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R L := dgOdotMilnorIdentityGluing_pretriangulated R d
local instance dgGluingIdentityInputConeTarget_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D := dgOdotMilnorIdentityDifference_pretriangulated R d
local instance dgGluingIdentityInputConeBase_stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R C
attribute [local irreducible] dgHomGluingBimodule

def dgGluingIdentityInputConeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputLaxEquivalence R d).hom ≫
      (exactLaxDifference
        (𝟙 (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)))
        (𝟙 (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)))).hom)
    ((dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)).hom ≫
      (dgOdotMilnorIdentityDifferenceValueEquivalence R d).hom) := by
  let eB := (dgOdotMilnorIdentityBase_nu_equivalence R d).choose
  let eG := (dgOdotMilnorIdentityGluing_nu_equivalence R d).choose
  let eN := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C
  let eL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence eB
  let v := dgKNativePerfectValueEquivalence R C
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgHomGluingConeFunctor R C C C I I)
  let δ₀ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)))
  let δ₁ := (exactLaxDifference
    (𝟙 (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)))
    (𝟙 (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)))).hom
  let a := (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)).hom
  let b := (dgOdotMilnorIdentityDifferenceValueEquivalence R d).hom
  let z : C := dgSmallPerfectBaseZero R _
  have hz : IsZero (ForgetEnrichment.of (Complex R) z) := dgSmallPerfectBaseZero_isZero R _
  have hc : eB.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R C) ≫ v.hom :=
    dgKNativeValueComparison_eq R C
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eN.hom ≫ δ₀ ≫ eB.hom) (f ≫ v.hom) := by
    have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeConeComparison R C
      (dgOdotMilnorIdentityBase_complete R d) z hz).postcomp v.hom
    refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h ?_ rfl
    change ((eN.hom ≫ δ₀) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R C)) ≫ v.hom = _
    exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
      (congrArg (fun k => eN.hom ≫ δ₀ ≫ k) hc.symm))
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eN.hom ≫ eL.hom ≫ δ₁) (eN.hom ≫ δ₀ ≫ eB.hom) := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseCofiberComparison eB).precomp eN.hom
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (eG.hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputLaxEquivalence R d).hom ≫ δ₁)
      (eN.hom ≫ eL.hom ≫ δ₁) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eG.hom ≫ (eG.inv ≫ eN.hom ≫ eL.hom) ≫ δ₁) _
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.id_comp] using
      eG.homInvIso.postcomp (eN.hom ≫ eL.hom ≫ δ₁)
  have hr₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eG.hom ≫ a ≫ b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDifference R d) ≫ dgKNativeValueComparison R D ≫ b) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((dgOdotMilnorIdentityDifference_nu_comparison R d).postcomp b)
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  have hr₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDifference R d) ≫ dgKNativeValueComparison R D ≫ b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDifference R d) ≫
        (dgSmallPerfectEnvelopeNerveEquivalence R C L
          (dgHomGluingConeFunctor R C C C I I).obj).hom ≫ v.hom) :=
    (dgOdotMilnorIdentityDifferenceValueEquivalence_native R d).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDifference R d))
  have heval : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDifference R d) ≫
      (dgSmallPerfectEnvelopeNerveEquivalence R C L
        (dgHomGluingConeFunctor R C C C I I).obj).hom = f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectFunctorImageLift R L C
      (dgHomGluingConeFunctor R C C C I I)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectEnvelopeInclusion R C L
        (dgHomGluingConeFunctor R C C C I I).obj) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgSmallPerfectFunctorImageLift_inclusion]
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eG.hom ≫ a ≫ b) (f ≫ v.hom) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (hr₁.trans hr₂) rfl
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ v.hom) heval))
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (eG.hom ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputLaxEquivalence R d).hom ≫ δ₁))
      (eG.hom ≫ (a ≫ b)) := (hg.trans (hb.trans hn)).trans hr.symm
  exact functorIsoReflectPreEquivalence eG h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
