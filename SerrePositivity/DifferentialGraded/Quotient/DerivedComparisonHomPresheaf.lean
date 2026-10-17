module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLocalObjects
public import Mathlib.CategoryTheory.Localization.Opposite

/-! # 制限代表加群への Hom を指定 Verdier 商へ降ろす -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商の制限代表加群への導来 Hom の反変関手。 -/
def quotientRestrictionHomPresheaf (S : Set D) (z : D) :
    (TriaCategory A D)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  (triaInclusion A D).op ⋙ yoneda.obj ((moduleToDerived A D).obj
    (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z)))

lemma quotientRestrictionHomPresheaf_inverts (S : Set D) (z : D) :
    (triaImage A D S).trW.op.IsInvertedBy (quotientRestrictionHomPresheaf A D S z) := by
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).2
  exact quotientRepresentableRestriction_tria_precomp_bijective A D S z f.unop hf

/-- U17a の指定 Verdier 商上に降りた、制限代表加群への Hom。 -/
def quotientRestrictionLocalizedHom (S : Set D) (z : D) :
    (TriaQuotient A D S)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  Localization.lift (quotientRestrictionHomPresheaf A D S z)
    (quotientRestrictionHomPresheaf_inverts A D S z) (triaQuotient A D S).op

/-- 元の tria 上への引き戻しは、元の導来 Hom そのもの。 -/
def quotientRestrictionLocalizedHomFactors (S : Set D) (z : D) :
    (triaQuotient A D S).op ⋙ quotientRestrictionLocalizedHom A D S z ≅
      quotientRestrictionHomPresheaf A D S z :=
  Localization.fac (quotientRestrictionHomPresheaf A D S z)
    (quotientRestrictionHomPresheaf_inverts A D S z) (triaQuotient A D S).op

/-- 商上の Hom 反変関手の値と実際の導来 Hom の計算同値。 -/
def quotientRestrictionLocalizedHomEquiv (S : Set D) (z : D) (X : TriaCategory A D) :
    (quotientRestrictionLocalizedHom A D S z).obj (op ((triaQuotient A D S).obj X)) ≃
      ((triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :=
  ((quotientRestrictionLocalizedHomFactors A D S z).app (op X)).toEquiv

/-- 計算同値は、元の tria の射に沿う前置と可換。 -/
lemma quotientRestrictionLocalizedHomEquiv_naturality (S : Set D) (z : D)
    {M N : TriaCategory A D} (s : M ⟶ N)
    (t : (quotientRestrictionLocalizedHom A D S z).obj
      (op ((triaQuotient A D S).obj N))) :
    quotientRestrictionLocalizedHomEquiv A D S z M
      ((quotientRestrictionLocalizedHom A D S z).map ((triaQuotient A D S).map s).op t) =
        (triaInclusion A D).map s ≫ quotientRestrictionLocalizedHomEquiv A D S z N t := by
  exact congrArg (fun k => k t)
    ((quotientRestrictionLocalizedHomFactors A D S z).hom.naturality s.op)

end SerrePositivity.DifferentialGraded.DGQuotient
