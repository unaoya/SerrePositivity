module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityInputLaxEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityHomTargetDiagonal
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet DifferentialGraded KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => DGOdotMilnorIdentityBase R d
local notation "L" => DGOdotMilnorIdentityGluing R d
local instance : IsDGPretriangulated R C := dgOdotMilnorIdentityBase_pretriangulated R d
local instance : IsDGPretriangulated R L := dgOdotMilnorIdentityGluing_pretriangulated R d

attribute [local irreducible] dgHomGluingBimodule

def dgGluingIdentityInputDiagonalIso : FunctorIso
    ((dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)).hom ≫
      (dgGluingIdentityInputLaxEquivalence R d).hom)
    (IdentityLax.exactDiagonal (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d))).hom := by
  let eB := (dgOdotMilnorIdentityBase_nu_equivalence R d).choose
  let eG := (dgOdotMilnorIdentityGluing_nu_equivalence R d).choose
  let eN := dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C
  let eL := identityLaxArrowBaseEquivalence eB
  let i := dgNerve.map (dgOdotMilnorIdentityDiagonal R d)
  let j := (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)).hom
  let z := (IdentityLax.exactDiagonal
    (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d))).hom
  have h₁ : FunctorIso (eB.hom ≫ j ≫ eG.inv ≫ eN.hom ≫ eL.hom)
      (i ≫ eG.hom ≫ eG.inv ≫ eN.hom ≫ eL.hom) := by
    exact F2.functorIsoOfEq
      ((dgOdotMilnorIdentityDiagonal_nu_comparison R d).postcomp (eG.inv ≫ eN.hom ≫ eL.hom))
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  have h₂ : FunctorIso (i ≫ eG.hom ≫ eG.inv ≫ eN.hom ≫ eL.hom)
      (i ≫ eN.hom ≫ eL.hom) := by
    simpa only [FunctorIso, Category.assoc, Category.comp_id] using
      (eG.homInvIso.precomp i).postcomp (eN.hom ≫ eL.hom)
  have h₃ : FunctorIso (i ≫ eN.hom ≫ eL.hom)
      ((constantFunctorMap (Δ[1] : SSet.{u + 1}) (dgNerve R C) ≫
        arrowLaxInverse (dgNerve R C)) ≫ eL.hom) := by
    exact F2.functorIsoOfEq ((dgGluingIdentityNativeDiagonalIso.{u, 0} R C).postcomp eL.hom)
      (Category.assoc _ _ _) rfl
  have h₄ : (constantFunctorMap (Δ[1] : SSet.{u + 1}) (dgNerve R C) ≫
      arrowLaxInverse (dgNerve R C)) ≫ eL.hom = eB.hom ≫ z :=
    identityLaxArrowBaseEquivalence_diagonal eB
  have h : FunctorIso (eB.hom ≫ (j ≫ (dgGluingIdentityInputLaxEquivalence R d).hom))
      (eB.hom ≫ z) :=
    F2.functorIsoOfEq (h₁.trans (h₂.trans h₃)) rfl h₄
  exact functorIsoReflectPreEquivalence eB h

end SerrePositivity.InfinityCategories
