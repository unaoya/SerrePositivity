module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityInputLaxEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityHomTargetDiagonal
public import SerrePositivity.KST.SConstruction.FunctorIsoEquivalenceReflection
/-!
概要：恒等 Hom gluing の指定固定入力対角を、恒等 lax 対角へ全関手同型で比較する。
方針：元の native 対角比較を全 ν 自然性と指定同値の往復則で運び、始域同値で反映する。
規約：指定された中央同値を使う。使われ方：恒等比較入力の diagonal 欄。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalClosed SSet DifferentialGraded KST.SConstruction
open _root_.SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => DGOdotMilnorIdentityBase R d
local notation "L" => DGOdotMilnorIdentityGluing R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C := dgOdotMilnorIdentityBase_pretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R L := dgOdotMilnorIdentityGluing_pretriangulated R d

attribute [local irreducible] dgHomGluingBimodule

def dgGluingIdentityInputDiagonalIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputLaxEquivalence R d).hom)
    (IdentityLax.exactDiagonal (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d))).hom := by
  let eB := (dgOdotMilnorIdentityBase_nu_equivalence R d).choose
  let eG := (dgOdotMilnorIdentityGluing_nu_equivalence R d).choose
  let eN := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C
  let eL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence eB
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDiagonal R d)
  let j := (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)).hom
  let z := (IdentityLax.exactDiagonal
    (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d))).hom
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eB.hom ≫ j ≫ eG.inv ≫ eN.hom ≫ eL.hom)
      (i ≫ eG.hom ≫ eG.inv ≫ eN.hom ≫ eL.hom) := by
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((dgOdotMilnorIdentityDiagonal_nu_comparison R d).postcomp (eG.inv ≫ eN.hom ≫ eL.hom))
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ eG.hom ≫ eG.inv ≫ eN.hom ≫ eL.hom)
      (i ≫ eN.hom ≫ eL.hom) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.comp_id] using
      (eG.homInvIso.precomp i).postcomp (eN.hom ≫ eL.hom)
  have h₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ eN.hom ≫ eL.hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) ≫ eL.hom) := by
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonalIso.{u, 0} R C).postcomp eL.hom)
      (Category.assoc _ _ _) rfl
  have h₄ : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) ≫ eL.hom = eB.hom ≫ z :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence_diagonal eB
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eB.hom ≫ (j ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityInputLaxEquivalence R d).hom))
      (eB.hom ≫ z) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (h₁.trans (h₂.trans h₃)) rfl h₄
  exact functorIsoReflectPreEquivalence eB h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
