module
public import SerrePositivity.HomologicalAlgebra.FiniteCohomologyBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology

/-! # Derived scalar extension of Tor-acyclic single objects in every degree -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- A module in any specified degree of the standard bounded-above derived category. -/
def boundedAboveDerivedSingleAt (i : ℤ) :
    ModuleCat.{u} R ⥤ DerivedCategory.Minus (ModuleCat.{u} R) where
  obj M := ⟨(DerivedCategory.singleFunctor (ModuleCat R) i).obj M, ⟨i, inferInstance⟩⟩
  map f := ObjectProperty.homMk ((DerivedCategory.singleFunctor (ModuleCat R) i).map f)
  map_id M := by
    apply InducedCategory.hom_ext
    exact (DerivedCategory.singleFunctor (ModuleCat R) i).map_id M
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (DerivedCategory.singleFunctor (ModuleCat R) i).map_comp f g

/-- The bounded-above single object in degree i is the shift by -i of the zero-degree object. -/
def boundedAboveDerivedSingleShiftIso (i : ℤ) :
    boundedAboveDerivedSingleFunctor (R := R) ⋙
        shiftFunctor (DerivedCategory.Minus (ModuleCat R)) (-i) ≅
      boundedAboveDerivedSingleAt R i := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    ((DerivedCategory.Minus.ι.commShiftIso (-i)).app (boundedAboveDerivedSingleFunctor.obj M) ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-i) i 0 (by omega)).app M)) ?_
  intro M N f
  apply InducedCategory.hom_ext
  have hn := (DerivedCategory.Minus.ι.commShiftIso (-i)).hom.naturality
    (boundedAboveDerivedSingleFunctor.map f)
  have hs := ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso
    (-i) i 0 (by omega)).hom.naturality f
  change ((boundedAboveDerivedSingleFunctor.map f)⟦-i⟧').hom ≫
    (DerivedCategory.Minus.ι.commShiftIso (-i)).hom.app _ =
      (DerivedCategory.Minus.ι.commShiftIso (-i)).hom.app _ ≫
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).map f)⟦-i⟧' at hn
  change ((DerivedCategory.singleFunctor (ModuleCat R) 0).map f)⟦-i⟧' ≫
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-i) i 0 (by omega)).hom.app N =
      ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-i) i 0 (by omega)).hom.app M ≫
        (DerivedCategory.singleFunctor (ModuleCat R) i).map f at hs
  simp only [ObjectProperty.isoMk, Iso.trans_hom, Iso.app_hom, ObjectProperty.homMk_hom,
    ObjectProperty.FullSubcategory.comp_hom, Functor.comp_map, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc, hs]
  rfl

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

/-- Tor-acyclic modules in any degree compare by the shifted standard augmentation. -/
def boundedAboveDerivedBaseChangeSingleIso (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) (i : ℤ) :
    ((boundedAboveDerivedBaseChange φ).obj ((boundedAboveDerivedSingleAt R i).obj M)).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat S) i).obj ((ModuleCat.extendScalars φ).obj M) :=
  DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange φ).mapIso
      ((boundedAboveDerivedSingleShiftIso R i).app M).symm) ≪≫
    boundedAboveDerivedBaseChangeAcyclicShiftIso φ M hM (-i) ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat S)).shiftIso (-i) i 0 (by omega)).app
        ((ModuleCat.extendScalars φ).obj M)

lemma boundedAboveDerivedBaseChangeSingleIso_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : scalarExtensionTorVanishing φ M) (hN : scalarExtensionTorVanishing φ N) (i : ℤ) :
    ((boundedAboveDerivedBaseChange φ).map ((boundedAboveDerivedSingleAt R i).map f)).hom ≫
        (boundedAboveDerivedBaseChangeSingleIso φ N hN i).hom =
      (boundedAboveDerivedBaseChangeSingleIso φ M hM i).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat S) i).map
          ((ModuleCat.extendScalars φ).map f) := by
  have h₁ := congrArg (fun t => ((boundedAboveDerivedBaseChange φ).map t).hom)
    ((boundedAboveDerivedSingleShiftIso R i).inv.naturality f)
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at h₁
  have h₂ := boundedAboveDerivedBaseChangeAcyclicShiftIso_naturality φ f hM hN (-i)
  have h₃ := ((DerivedCategory.singleFunctors (ModuleCat S)).shiftIso
    (-i) i 0 (by omega)).hom.naturality ((ModuleCat.extendScalars φ).map f)
  change (((boundedAboveDerivedSingleFunctor.map ((ModuleCat.extendScalars φ).map f)).hom)⟦-i⟧') ≫
      ((DerivedCategory.singleFunctors (ModuleCat S)).shiftIso (-i) i 0 (by omega)).hom.app _ =
    ((DerivedCategory.singleFunctors (ModuleCat S)).shiftIso (-i) i 0 (by omega)).hom.app _ ≫
      (DerivedCategory.singleFunctor (ModuleCat S) i).map ((ModuleCat.extendScalars φ).map f) at h₃
  simp only [boundedAboveDerivedBaseChangeSingleIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  erw [h₁]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (((DerivedCategory.singleFunctors (ModuleCat S)).shiftIso
    (-i) i 0 (by omega)).hom.app ((ModuleCat.extendScalars φ).obj N))]
  erw [h₂]
  simp only [Category.assoc]
  rw [h₃]
  rfl

/-- The normalized actual homology comparison lifted to the bounded-above category. -/
def boundedAbovePureHomologyIso (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ)
    [X.obj.IsGE i] [X.obj.IsLE i] :
    X ≅ (boundedAboveDerivedSingleAt R i).obj
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj) :=
  ObjectProperty.isoMk _ (normalizedPureHomologyIso X.obj i)

lemma boundedAbovePureHomologyIso_naturality (i : ℤ)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)}
    [X.obj.IsGE i] [X.obj.IsLE i] [Y.obj.IsGE i] [Y.obj.IsLE i] (f : X ⟶ Y) :
    f ≫ (boundedAbovePureHomologyIso Y i).hom =
      (boundedAbovePureHomologyIso X i).hom ≫ (boundedAboveDerivedSingleAt R i).map
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).map f.hom) := by
  apply InducedCategory.hom_ext
  exact normalizedPureHomologyIso_naturality i f.hom

/-- Pure Tor-acyclic objects compare with ordinary scalar extension of their actual homology. -/
def boundedAboveDerivedBaseChangePureIso
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) [X.obj.IsGE i] [X.obj.IsLE i]
    (hX : scalarExtensionTorVanishing φ
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj)) :
    ((boundedAboveDerivedBaseChange φ).obj X).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat S) i).obj ((ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj)) :=
  DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange φ).mapIso
    (boundedAbovePureHomologyIso X i)) ≪≫ boundedAboveDerivedBaseChangeSingleIso φ _ hX i

lemma boundedAboveDerivedBaseChangePureIso_naturality (i : ℤ)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)}
    [X.obj.IsGE i] [X.obj.IsLE i] [Y.obj.IsGE i] [Y.obj.IsLE i] (f : X ⟶ Y)
    (hX : scalarExtensionTorVanishing φ
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj))
    (hY : scalarExtensionTorVanishing φ
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj Y.obj)) :
    ((boundedAboveDerivedBaseChange φ).map f).hom ≫
        (boundedAboveDerivedBaseChangePureIso φ Y i hY).hom =
      (boundedAboveDerivedBaseChangePureIso φ X i hX).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat S) i).map ((ModuleCat.extendScalars φ).map
          ((DerivedCategory.homologyFunctor (ModuleCat R) i).map f.hom)) := by
  have hn := congrArg (fun t => ((boundedAboveDerivedBaseChange φ).map t).hom)
    (boundedAbovePureHomologyIso_naturality i f)
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at hn
  simp only [boundedAboveDerivedBaseChangePureIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [← Category.assoc]
  erw [hn]
  simp only [Category.assoc]
  rw [boundedAboveDerivedBaseChangeSingleIso_naturality]
  rfl

/-- The natural homology comparison for a pure Tor-acyclic object. -/
def boundedAboveDerivedBaseChangePureHomologyIso
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) [X.obj.IsGE i] [X.obj.IsLE i]
    (hX : scalarExtensionTorVanishing φ
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj)) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj X).obj ≅
      (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
      (boundedAboveDerivedBaseChangePureIso φ X i hX) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) i).app _

lemma boundedAboveDerivedBaseChangePureHomologyIso_naturality (i : ℤ)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)}
    [X.obj.IsGE i] [X.obj.IsLE i] [Y.obj.IsGE i] [Y.obj.IsLE i] (f : X ⟶ Y)
    (hX : scalarExtensionTorVanishing φ
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj))
    (hY : scalarExtensionTorVanishing φ
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj Y.obj)) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        ((boundedAboveDerivedBaseChange φ).map f).hom ≫
        (boundedAboveDerivedBaseChangePureHomologyIso φ Y i hY).hom =
      (boundedAboveDerivedBaseChangePureHomologyIso φ X i hX).hom ≫
        (ModuleCat.extendScalars φ).map
          ((DerivedCategory.homologyFunctor (ModuleCat R) i).map f.hom) := by
  simp only [boundedAboveDerivedBaseChangePureHomologyIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp,
    boundedAboveDerivedBaseChangePureIso_naturality φ i f hX hY, Functor.map_comp, Category.assoc]
  congr 1
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) i).hom.naturality _

end SerrePositivity
