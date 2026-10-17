module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonAdjointUnit
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonRepresentableHom

/-! # Verdier Hom 同値と実際の導来延長の射写像

随伴の単位による代表同型の正規化を、局所 K-flat Hom 同値と接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientDerivedRepresentableHomEquiv_adjoint (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S)
      ((triaInclusion A D).obj X)
      ((moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S))))
      (quotientDerivedRepresentableHomEquiv A D S h z X f) =
    quotientRepresentableHomMap A D S z X f ≫
      (dgDerivedRestrictionComputation A D (QuotientObject D S) (inclusion A D S)
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S)))).inv := by
  simp only [quotientDerivedRepresentableHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Iso.homCongr, Equiv.coe_fn_mk, quotientRepresentableHomEquiv, Equiv.ofBijective_apply,
    Iso.refl_inv, Category.id_comp, Iso.symm_hom]

/-- 元の tria の射に対し、Hom 同値は実際の導来延長の射写像と一致する。 -/
lemma quotientDerivedRepresentableHomEquiv_map (S : Set D) (h : localKFlat A D S)
    (z : D) {X : TriaCategory A D} (f : X ⟶ triaRepresentable A D z) :
    quotientDerivedRepresentableHomEquiv A D S h z X ((triaQuotient A D S).map f) =
      (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).map
        ((triaInclusion A D).map f) ≫
      (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom := by
  apply (dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S) _ _).injective
  rw [quotientDerivedRepresentableHomEquiv_adjoint,
    dgDerivedExtensionHomEquiv_naturality_left,
    quotientRepresentableHomMap_map, Category.assoc]
  exact congrArg (fun t => (triaInclusion A D).map f ≫ t)
    (derivedExtensionRepresentableUnitIso_homEquiv A D (QuotientObject D S)
      (inclusion A D S) z).symm

/-- Verdier 商の任意の射に対する Hom 同値も、元の tria の射による前置と可換。 -/
lemma quotientDerivedRepresentableHomEquiv_precomp (S : Set D) (h : localKFlat A D S)
    (z : D) {X Y : TriaCategory A D} (s : X ⟶ Y)
    (f : (triaQuotient A D S).obj Y ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    quotientDerivedRepresentableHomEquiv A D S h z X ((triaQuotient A D S).map s ≫ f) =
      (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).map
        ((triaInclusion A D).map s) ≫ quotientDerivedRepresentableHomEquiv A D S h z Y f := by
  apply (dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S) _ _).injective
  rw [quotientDerivedRepresentableHomEquiv_adjoint,
    dgDerivedExtensionHomEquiv_naturality_left, quotientDerivedRepresentableHomEquiv_adjoint,
    quotientRepresentableHomMap_precomp, Category.assoc]

end SerrePositivity.DifferentialGraded.DGQuotient
