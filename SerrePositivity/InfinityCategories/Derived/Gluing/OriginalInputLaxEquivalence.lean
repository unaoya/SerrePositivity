module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OriginalInputLaxLegComparisons
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDerivedLaxEquivalence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCospanIsoEquivalence
/-!
概要：元 Hom 終域比較を固定入力の元二脚の lax 模型へ接続する。
方針：元終域の実逆と、指定入力同値を保つ cospan 全比較を合成する。
規約：左右射影は全関手同型で指定する。使われ方：K-S• の元二脚供給入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded KST.SConstruction SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgAlgebraCategory R d.source
local notation "B" => dgAlgebraCategory R d.left
local notation "C" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "L" => dgAlgebraMap R d.top
local notation "G" => dgAlgebraMap R d.side
local notation "p" => dgAlgebraMap R d.lower
local notation "q" => dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R A B L
local notation "DR" => DGSmallPerfectArrowTarget R A C G
local notation "V" => DGOdotCorner R d
local notation "P" => dgSmallPerfectSquareLeftMap R A B C E L G p q
local notation "Q" => dgSmallPerfectSquareRightMap R A B C E L G p q

def dgGluingOriginalInputLaxCospanEquivalence :=
  F2.laxPullbackCospanIsoEquivalence (dgNerve.map P) (dgNerve.map Q)
    (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
    (dgGluingOriginalLaxLeftEquivalence R d).hom
    (dgGluingOriginalLaxRightEquivalence R d).hom
    (dgGluingOriginalLaxCornerEquivalence R d).hom
    (dgGluingOriginalLaxLeftLeg R d) (dgGluingOriginalLaxRightLeg R d)
    (dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
    (dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
    (dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence

def dgGluingOriginalInputLaxEquivalence :
    QCatEquivalence (dgOdotMilnorLaxCategory R d).obj (dgOdotPerfLaxCategory R d).obj :=
  (dgGluingHomTargetDerivedLaxEquivalence.{u, 0} R CL DR V P Q).trans
    (dgGluingOriginalInputLaxCospanEquivalence R d)

def dgGluingOriginalInputLaxEquivalence_fst : FunctorIso
    ((dgGluingOriginalInputLaxEquivalence R d).hom ≫
      (laxFst (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((laxFst (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
      (dgOdotMilnorLaxLeftInputEquivalence R d).inv) := by
  let e := dgGluingHomTargetDerivedLaxEquivalence.{u, 0} R CL DR V P Q
  have h₁ := (F2.laxPullbackCospanIsoEquivalence_fst (dgNerve.map P) (dgNerve.map Q)
    (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
    (dgGluingOriginalLaxLeftEquivalence R d).hom
    (dgGluingOriginalLaxRightEquivalence R d).hom
    (dgGluingOriginalLaxCornerEquivalence R d).hom
    (dgGluingOriginalLaxLeftLeg R d) (dgGluingOriginalLaxRightLeg R d)
    (dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
    (dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
    (dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence).precomp e.hom
  have h₂ := (dgGluingHomTargetDerivedLaxEquivalence_fst.{u, 0} R CL DR V P Q).postcomp
    (dgGluingOriginalLaxLeftEquivalence R d).hom
  have h := h₁.trans (F2.functorIsoOfEq h₂ (Category.assoc _ _ _) rfl)
  have hc : (dgGluingNativeUniverseIso (dgNerve R CL)).inv ≫
      (dgGluingOriginalLaxLeftEquivalence R d).hom =
        (dgOdotMilnorLaxLeftInputEquivalence R d).inv := by
    rw [← dgGluingOriginalLaxLeftEquivalence_input, Iso.inv_hom_id_assoc]
  refine F2.functorIsoOfEq h ?_ ?_
  · exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hc]; rfl

def dgGluingOriginalInputLaxEquivalence_snd : FunctorIso
    ((dgGluingOriginalInputLaxEquivalence R d).hom ≫
      (laxSnd (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((laxSnd (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
      (dgOdotMilnorLaxRightInputEquivalence R d).inv) := by
  let e := dgGluingHomTargetDerivedLaxEquivalence.{u, 0} R CL DR V P Q
  have h₁ := (F2.laxPullbackCospanIsoEquivalence_snd (dgNerve.map P) (dgNerve.map Q)
    (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
    (dgGluingOriginalLaxLeftEquivalence R d).hom
    (dgGluingOriginalLaxRightEquivalence R d).hom
    (dgGluingOriginalLaxCornerEquivalence R d).hom
    (dgGluingOriginalLaxLeftLeg R d) (dgGluingOriginalLaxRightLeg R d)
    (dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
    (dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
    (dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence).precomp e.hom
  have h₂ := (dgGluingHomTargetDerivedLaxEquivalence_snd.{u, 0} R CL DR V P Q).postcomp
    (dgGluingOriginalLaxRightEquivalence R d).hom
  have h := h₁.trans (F2.functorIsoOfEq h₂ (Category.assoc _ _ _) rfl)
  have hc : (dgGluingNativeUniverseIso (dgNerve R DR)).inv ≫
      (dgGluingOriginalLaxRightEquivalence R d).hom =
        (dgOdotMilnorLaxRightInputEquivalence R d).inv := by
    rw [← dgGluingOriginalLaxRightEquivalence_input, Iso.inv_hom_id_assoc]
  refine F2.functorIsoOfEq h ?_ ?_
  · exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hc]; rfl

def dgGluingOriginalLaxComparisonInput : DGOdotMilnorOriginalLaxComparisonInput R d where
  gluing := dgGluingOriginalInputLaxEquivalence R d
  fst := dgGluingOriginalInputLaxEquivalence_fst R d
  snd := dgGluingOriginalInputLaxEquivalence_snd R d

end SerrePositivity.InfinityCategories
