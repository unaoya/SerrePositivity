module
public import SerrePositivity.HomologicalAlgebra.ChainLinearYoneda
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Natural computation of Mathlib's Ext using a specified projective resolution -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Ext computed by a specified projective resolution is natural in the coefficient module. -/
lemma projectiveResolutionIsoExt_naturality {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Ext R (ModuleCat R) i).obj (op X)).map f ≫ (P.isoExt i N).hom =
      (P.isoExt i M).hom ≫
        homologyMap ((chainLinearYonedaFunctor P.complex).map f) i := by
  let FM := ((linearYoneda R (ModuleCat R)).obj M).rightOp
  let FN := ((linearYoneda R (ModuleCat R)).obj N).rightOp
  let β : FN ⟶ FM := ((linearYoneda R (ModuleCat R)).map f).rightOp
  let KM := (FM.mapHomologicalComplex (.down ℕ)).obj P.complex
  let KN := (FN.mapHomologicalComplex (.down ℕ)).obj P.complex
  let b : KN ⟶ KM := (NatTrans.mapHomologicalComplex β (.down ℕ)).app P.complex
  change ((NatTrans.leftDerived β i).app X).unop ≫
      ((P.isoLeftDerivedObj FN i).inv.unop ≫ (homologyUnop KN i).inv) =
    ((P.isoLeftDerivedObj FM i).inv.unop ≫ (homologyUnop KM i).inv) ≫
      homologyMap ((chainLinearYonedaFunctor P.complex).map f) i
  rw [P.leftDerived_app_eq β i]
  simp only [unop_comp, Category.assoc]
  have hc : (P.isoLeftDerivedObj FN i).hom.unop ≫ (P.isoLeftDerivedObj FN i).inv.unop =
      𝟙 _ := by simp only [← unop_comp, Iso.inv_hom_id, unop_id]
  rw [← Category.assoc (P.isoLeftDerivedObj FN i).hom.unop
    (P.isoLeftDerivedObj FN i).inv.unop (homologyUnop KN i).inv, hc, Category.id_comp]
  have hn := chainHomologyUnop_inv_naturality b i
  change (homologyMap b i).unop ≫ (homologyUnop KN i).inv =
    (homologyUnop KM i).inv ≫
      homologyMap ((chainLinearYonedaFunctor P.complex).map f) i at hn
  erw [hn]

/-- A functorial Ext computation, rather than unrelated isomorphisms for individual modules. -/
def projectiveResolutionExtNatIso {X : ModuleCat.{u} R} (P : ProjectiveResolution X) (i : ℕ) :
    (Ext R (ModuleCat R) i).obj (op X) ≅
      chainLinearYonedaFunctor P.complex ⋙ homologyFunctor (ModuleCat R) (.up ℕ) i :=
  NatIso.ofComponents (fun M => P.isoExt i M)
    (fun f => projectiveResolutionIsoExt_naturality P i f)

/-- The computation respects any augmented lift of a morphism in Ext's first argument. -/
lemma projectiveResolutionIsoExt_first_naturality
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (M : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat R) i).map f.op).app M ≫ (P.isoExt i M).hom =
      (Q.isoExt i M).hom ≫ homologyMap ((chainLinearYonedaMap φ).app M) i := by
  let F := ((linearYoneda R (ModuleCat R)).obj M).rightOp
  let KP := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let KQ := (F.mapHomologicalComplex (.down ℕ)).obj Q.complex
  let b : KP ⟶ KQ := (F.mapHomologicalComplex (.down ℕ)).map φ
  have hn := congrArg Quiver.Hom.unop
    (ProjectiveResolution.isoLeftDerivedObj_inv_naturality f P Q φ hφ F i)
  change ((F.leftDerived i).map f).unop ≫ (P.isoLeftDerivedObj F i).inv.unop =
    (Q.isoLeftDerivedObj F i).inv.unop ≫ (homologyMap b i).unop at hn
  change ((F.leftDerived i).map f).unop ≫
      ((P.isoLeftDerivedObj F i).inv.unop ≫ (homologyUnop KP i).inv) =
    ((Q.isoLeftDerivedObj F i).inv.unop ≫ (homologyUnop KQ i).inv) ≫
      homologyMap ((chainLinearYonedaMap φ).app M) i
  rw [← Category.assoc, hn, Category.assoc]
  have hu := chainHomologyUnop_inv_naturality b i
  change (homologyMap b i).unop ≫ (homologyUnop KP i).inv =
    (homologyUnop KQ i).inv ≫ homologyMap ((chainLinearYonedaMap φ).app M) i at hu
  rw [hu]
  simp only [Category.assoc]

end SerrePositivity
