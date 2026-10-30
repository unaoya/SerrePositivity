module
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-! # Upper bounds and shifted Tor-acyclic modules for actual derived scalar extension -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

/-- Left derivation preserves every upper cohomology bound, even for a nonexact functor. -/
lemma boundedAboveLeftDerived_isLE
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {E : Type u'} [Category.{v'} E] [Abelian E] (F : C ⥤ E) [F.Additive]
    (X : DerivedCategory.Minus C) (i : ℤ) [X.obj.IsLE i] :
    ((boundedAboveLeftDerived F).obj X).obj.IsLE i := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X.obj i
  obtain ⟨L, ε, hε, hL, hb⟩ := exists_boundedAbove_projective_resolution K i
  have : QuasiIso ε := hε
  let P : BoundedAboveDerivedModel X.obj :=
    ⟨L, i, hb, hL, asIso (DerivedCategory.Q.map ε) ≪≫ e.symm⟩
  have : P.complex.IsStrictlyLE i := hb
  have : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) i :=
    inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (boundedAboveLeftDerivedModelIso F X P).symm i

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Every shift of a Tor-acyclic module has the expected actual derived scalar extension. -/
def boundedAboveDerivedBaseChangeAcyclicShiftIso (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) (n : ℤ) :
    ((boundedAboveDerivedBaseChange φ).obj
      ((boundedAboveDerivedSingleFunctor.obj M)⟦n⟧)).obj ≅
      (((boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj M)).obj)⟦n⟧) :=
  boundedAboveLeftDerivedShiftIso (ModuleCat.extendScalars φ)
      (boundedAboveDerivedSingleFunctor.obj M) n ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat S)) n).mapIso
      (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedBaseChangeModuleAugmentationIso φ M hM))

lemma boundedAboveDerivedBaseChangeAcyclicShiftIso_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : scalarExtensionTorVanishing φ M) (hN : scalarExtensionTorVanishing φ N) (n : ℤ) :
    ((boundedAboveDerivedBaseChange φ).map
        ((boundedAboveDerivedSingleFunctor.map f)⟦n⟧')).hom ≫
        (boundedAboveDerivedBaseChangeAcyclicShiftIso φ N hN n).hom =
      (boundedAboveDerivedBaseChangeAcyclicShiftIso φ M hM n).hom ≫
        (((boundedAboveDerivedSingleFunctor.map ((ModuleCat.extendScalars φ).map f)).hom)⟦n⟧') := by
  have hs := boundedAboveLeftDerivedShiftIso_naturality (ModuleCat.extendScalars φ)
    (boundedAboveDerivedSingleFunctor.map f) n
  have hm := boundedAboveDerivedBaseChangeModuleAugmentationIso_naturality φ f hM hN
  have hm' := congrArg (fun t => t.hom) hm
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hm'
  simp only [boundedAboveDerivedBaseChangeAcyclicShiftIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  dsimp only [boundedAboveDerivedBaseChange] at hm' ⊢
  rw [← Category.assoc, hs, Category.assoc, ← Functor.map_comp]
  erw [hm']
  rw [Functor.map_comp]
  rfl

/-- Tor-acyclicity gives the lower bound needed for the finite cohomology induction. -/
lemma boundedAboveDerivedBaseChangeAcyclicShift_isGE (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) (n : ℤ) :
    ((boundedAboveDerivedBaseChange φ).obj
      ((boundedAboveDerivedSingleFunctor.obj M)⟦n⟧)).obj.IsGE (-n) := by
  let Y := (boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj M)).obj
  have : Y.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.extendScalars φ).obj M)).IsGE 0
    infer_instance
  have : (Y⟦n⟧).IsGE (-n) := DerivedCategory.TStructure.t.isGE_shift Y 0 n (-n) (by omega)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (boundedAboveDerivedBaseChangeAcyclicShiftIso φ M hM n).symm (-n)

end SerrePositivity
