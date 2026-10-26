module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNativeConeComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.OriginalInputLaxEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxCospanIsoCofiberComparison
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeZero
/-! 元二脚の指定全 lax 比較と固定 corner 評価を持つ、元実 cone の全比較入力。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet DifferentialGraded KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
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
local instance dgGluingOriginalInputConeBase_pretriangulated : IsDGPretriangulated R V :=
  dgOdotMilnorCorner_pretriangulated R d
local instance dgGluingOriginalInputConeBase_stable : IsStable (dgNerve R V) :=
  dgNerve_isStable_of_pretriangulated R V
attribute [local irreducible] dgHomGluingBimodule

def dgGluingOriginalInputConeIso : FunctorIso
    ((dgOdotMilnorNativeLaxComparison R d).hom ≫
      ((dgGluingOriginalLaxComparisonInput R d).gluing.hom ≫
        (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom))
    (dgNerve.map (dgOdotTargetFunctor R d) ≫ (dgOdotMilnorCornerEvaluation R d).hom) := by
  let e := dgGluingHomTargetNativeDerivedLaxEquivalence.{u, 0} R CL DR V P Q
  let n := dgGluingHomTargetNerveLaxComparison.{u, 0} R CL DR V P Q
  let t := dgGluingOriginalInputLaxCospanEquivalence R d
  let c := (dgGluingOriginalLaxCornerEquivalence R d).hom
  let v := (dgOdotMilnorCornerEvaluation R d).hom
  let y := dgNerve.map (dgPerfectYoneda R V)
  let f := dgNerve.map (dgHomGluingConeFunctor R CL DR V P Q)
  let δ₀ := CofiberFamily.cofiber (dgNerve R V)
    (F2.laxPullbackArrow (dgNerve.map P) (dgNerve.map Q))
  let δ₁ := (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom
  have h₀ : FunctorIso
      ((dgOdotMilnorNativeLaxComparison R d).hom ≫
        ((dgGluingOriginalLaxComparisonInput R d).gluing.hom ≫ δ₁))
      (n ≫ t.hom ≫ δ₁) := by
    change FunctorIso (e.hom ≫ (((e.inv ≫ n) ≫ t.hom) ≫ δ₁)) _
    simpa only [FunctorIso, Category.assoc, Category.id_comp] using
      e.homInvIso.postcomp (n ≫ t.hom ≫ δ₁)
  have h₁ : FunctorIso (n ≫ t.hom ≫ δ₁) (n ≫ δ₀ ≫ c) := by
    exact (laxCospanIsoCofiberComparison (dgNerve.map P) (dgNerve.map Q)
      (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
      (dgGluingOriginalLaxLeftEquivalence R d).hom
      (dgGluingOriginalLaxRightEquivalence R d).hom c
      (dgGluingOriginalLaxLeftLeg R d) (dgGluingOriginalLaxRightLeg R d)
      (dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
      (dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
      (dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence).precomp n
  let z : V := dgSmallPerfectEnvelopeZero R _ _ _
  have hz : IsZero (ForgetEnrichment.of (Complex R) z) :=
    dgSmallPerfectEnvelopeZero_isZero R _ _ _
  have hn : FunctorIso (((n ≫ δ₀) ≫ y) ≫ v) (f ≫ v) :=
    (dgGluingHomTargetNativeConeComparison R CL DR V P Q
      (dgOdotMilnorCorner_complete R d) z hz).postcomp v
  have hy : FunctorIso ((n ≫ δ₀) ≫ c) ((n ≫ δ₀) ≫ (y ≫ v)) :=
    FunctorIso.precomp (dgOdotMilnorCornerEvaluation_yoneda R d).symm (n ≫ δ₀)
  have hn' : FunctorIso ((n ≫ δ₀) ≫ (y ≫ v)) (f ≫ v) :=
    F2.functorIsoOfEq hn (Category.assoc _ _ _) rfl
  have h₂ : FunctorIso (n ≫ δ₀ ≫ c) (f ≫ v) :=
    F2.functorIsoOfEq (hy.trans hn') (Category.assoc _ _ _) rfl
  exact h₀.trans (h₁.trans h₂)

def dgGluingOriginalLaxConeComparisonInput : DGOdotMilnorOriginalLaxConeComparisonInput R d :=
  (dgGluingOriginalLaxComparisonInput R d).withCone R d (dgGluingOriginalInputConeIso R d)

end SerrePositivity.InfinityCategories
