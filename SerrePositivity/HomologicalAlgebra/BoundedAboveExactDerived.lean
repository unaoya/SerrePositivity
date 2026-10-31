module
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import SerrePositivity.CategoryTheory.ExactDerivedTStructure

/-! # Exact functors on the standard bounded-above derived categories -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]
variable (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor preserves the standard upper cohomological bounds. -/
lemma exactDerived_isLE (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n :=
  Functor.isLE_obj F.mapDerivedCategory (DerivedCategory.TStructure.t (C := C))
    (DerivedCategory.TStructure.t (C := E)) X n

/-- The standard derived functor of an exact functor restricts to the bounded-above categories. -/
def boundedAboveExactDerived : DerivedCategory.Minus C ⥤ DerivedCategory.Minus E :=
  DerivedCategory.TStructure.t.minus.lift (DerivedCategory.Minus.ι ⋙ F.mapDerivedCategory) (by
    intro X
    obtain ⟨n, hn⟩ := X.property
    exact ⟨n, exactDerived_isLE F X.obj n⟩)

/-- Compute the exact derived functor with any specified projective model. -/
def boundedAboveExactDerivedModelIso (X : DerivedCategory.Minus C)
    (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveExactDerived F).obj X).obj ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) :=
  F.mapDerivedCategory.mapIso P.iso.symm ≪≫ F.mapDerivedCategoryFactors.app P.complex

/-- The model computation is natural in arbitrary representatives of the derived morphism. -/
lemma boundedAboveExactDerivedModelIso_naturality {X Y : DerivedCategory.Minus C}
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f.hom) :
    ((boundedAboveExactDerived F).map f).hom ≫ (boundedAboveExactDerivedModelIso F Y Q).hom =
      (boundedAboveExactDerivedModelIso F X P).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map h) := by
  have he : f.hom ≫ Q.iso.inv = P.iso.inv ≫ DerivedCategory.Q.map h := by
    apply (cancel_epi P.iso.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← hh]
    simp
  change F.mapDerivedCategory.map f.hom ≫
      (F.mapDerivedCategory.map Q.iso.inv ≫ F.mapDerivedCategoryFactors.hom.app Q.complex) =
    (F.mapDerivedCategory.map P.iso.inv ≫ F.mapDerivedCategoryFactors.hom.app P.complex) ≫ _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, he,
    CategoryTheory.Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality]
  simp only [Category.assoc]

/-- Resolving first gives the standard exact derived functor, naturally in all derived objects. -/
def boundedAboveLeftDerivedExactIso [EnoughProjectives C] :
    boundedAboveLeftDerived F ≅ boundedAboveExactDerived F := by
  refine NatIso.ofComponents (fun X => ObjectProperty.isoMk _
    (boundedAboveExactDerivedModelIso F X (boundedAboveDerivedChosenModel X)).symm) ?_
  intro X Y f
  apply InducedCategory.hom_ext
  apply (cancel_mono (boundedAboveExactDerivedModelIso F Y
    (boundedAboveDerivedChosenModel Y)).hom).mp
  have hn := boundedAboveExactDerivedModelIso_naturality F
    (boundedAboveDerivedChosenModel X) (boundedAboveDerivedChosenModel Y) f
    ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom)
    (BoundedAboveDerivedModel.map_naturality _ _ f.hom)
  simp only [ObjectProperty.isoMk, ObjectProperty.homMk_hom, Iso.symm_hom,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hn]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- Exact functors commute with the homology of cochain complexes, naturally. -/
def exactCochainHomologyIso (n : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor E (.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F)
    (fun f => CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f) F)

/-- Homology comparison, natural in every object and morphism of the standard derived category. -/
def exactDerivedHomologyNatIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor E n ≅
      DerivedCategory.homologyFunctor C n ⋙ F := by
  let L := F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor E n
  let M := DerivedCategory.homologyFunctor C n ⋙ F
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      (DerivedCategory.Q ⋙ L) L := ⟨Iso.refl _⟩
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      (DerivedCategory.Q ⋙ M) M := ⟨Iso.refl _⟩
  apply Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ L) (DerivedCategory.Q ⋙ M) L M
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors E n) ≪≫
    exactCochainHomologyIso F n ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm _ ≪≫
    Functor.associator _ _ _

end SerrePositivity
