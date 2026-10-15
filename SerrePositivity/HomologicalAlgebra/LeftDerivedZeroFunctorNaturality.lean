module
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-! # Naturality of the zero-derived augmentation in the additive functor -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v₁ v₂ u₁ u₂
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {F G : C ⥤ D} [F.Additive] [G.Additive]

omit [EnoughProjectives C] in
/-- The opcycles augmentation is natural in the additive functor as well as its argument. -/
lemma projectiveResolution_fromLeftDerivedZero_functor_naturality
    (α : F ⟶ G) {X : C} (P : ProjectiveResolution X) :
    HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex α (.down ℕ)).app P.complex) 0 ≫
      P.fromLeftDerivedZero' G = P.fromLeftDerivedZero' F ≫ α.app X := by
  apply (cancel_epi (HomologicalComplex.pOpcycles
    ((F.mapHomologicalComplex (.down ℕ)).obj P.complex) 0)).mp
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  exact (α.naturality (P.π.f 0)).symm

/-- The actual zero-derived augmentation is natural in every additive functor morphism. -/
lemma fromLeftDerivedZero_functor_naturality (α : F ⟶ G) (X : C) :
    (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X =
      F.fromLeftDerivedZero.app X ≫ α.app X := by
  let P := projectiveResolution X
  rw [P.fromLeftDerivedZero_eq F, P.fromLeftDerivedZero_eq G,
    P.leftDerived_app_eq α 0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← projectiveResolution_fromLeftDerivedZero_functor_naturality α P]
  change (P.isoLeftDerivedObj F 0).hom ≫
    HomologicalComplex.homologyMap _ 0 ≫ HomologicalComplex.homologyι _ 0 ≫ _ =
    (P.isoLeftDerivedObj F 0).hom ≫ HomologicalComplex.homologyι _ 0 ≫
      HomologicalComplex.opcyclesMap _ 0 ≫ _
  rw [HomologicalComplex.homologyι_naturality_assoc]

end SerrePositivity
