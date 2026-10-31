module
public import SerrePositivity.HomologicalAlgebra.FiniteCohomologyBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.HomCongr

/-! # Actual maps from nonpositive derived objects to discrete objects -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Zero homology detects and realizes all maps between actual single derived objects. -/
lemma derivedSingleHomologyZero_map_bijective (M N : ModuleCat.{u} R) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N =>
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f) := by
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  have : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u} R) 0).Faithful := CategoryTheory.Functor.Faithful.of_iso E.symm
  constructor
  · intro f g h
    obtain ⟨f', rfl⟩ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map_surjective f
    obtain ⟨g', rfl⟩ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map_surjective g
    exact congrArg (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ DerivedCategory.homologyFunctor
      (ModuleCat.{u} R) 0).map_injective h)
  · intro f
    let eM := E.app M
    let eN := E.app N
    refine ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (eM.inv ≫ f ≫ eN.hom), ?_⟩
    apply (cancel_mono eN.hom).mp
    have hn := E.hom.naturality (eM.inv ≫ f ≫ eN.hom)
    change (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (eM.inv ≫ f ≫ eN.hom)) ≫ eN.hom =
      eM.hom ≫ (eM.inv ≫ f ≫ eN.hom) at hn
    simpa only [Iso.hom_inv_id_assoc] using hn

/-- Zero homology is fully faithful on pairs of actual heart objects. -/
lemma derivedHeartHomologyZero_map_bijective {X Y : DerivedCategory (ModuleCat.{u} R)}
    [X.IsLE 0] [X.IsGE 0] [Y.IsLE 0] [Y.IsGE 0] :
    Function.Bijective (fun f : X ⟶ Y => (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      f) := by
  obtain ⟨M, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0
  obtain ⟨N, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y 0
  have hb := derivedSingleHomologyZero_map_bijective M N
  constructor
  · intro f g h
    apply (cancel_epi eX.inv).mp
    apply (cancel_mono eY.hom).mp
    apply hb.injective
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, h]
  · intro f
    let eHX := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso eX
    let eHY := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso eY
    obtain ⟨g, hg⟩ := hb.surjective (eHX.inv ≫ f ≫ eHY.hom)
    refine ⟨eX.hom ≫ g ≫ eY.inv, ?_⟩
    dsimp only
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    change eHX.hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map g ≫ eHY.inv = f
    dsimp only at hg
    rw [hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- For a nonpositive source and a heart target, all actual derived morphisms
are uniquely determined by, and realize, their maps on zero homology. -/
lemma derivedNonpositiveHomologyZero_map_bijective {X Y : DerivedCategory (ModuleCat.{u} R)}
    [X.IsLE 0] [Y.IsLE 0] [Y.IsGE 0] :
    Function.Bijective (fun f : X ⟶ Y => (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      f) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat R)
  let B := (t.truncGE 0).obj X
  let η : X ⟶ B := (t.truncGEπ 0).app X
  have : B.IsLE 0 := by dsimp [B]; infer_instance
  have : B.IsGE 0 := by dsimp [B]; infer_instance
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map η) :=
    derivedTruncGE_homology_isIso X 0 0 (le_refl 0)
  have hb := derivedHeartHomologyZero_map_bijective (X := B) (Y := Y)
  constructor
  · intro f g h
    let f' := t.descTruncGE f 0
    let g' := t.descTruncGE g 0
    have hf : η ≫ f' = f := t.π_descTruncGE f 0
    have hg : η ≫ g' = g := t.π_descTruncGE g 0
    have hh : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f' =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map g' := by
      apply (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map η)).mp
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hf, hg]
      exact h
    calc
      f = η ≫ f' := hf.symm
      _ = η ≫ g' := congrArg (η ≫ ·) (hb.injective hh)
      _ = g := hg
  · intro f
    let e := asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map η)
    obtain ⟨g, hg⟩ := hb.surjective (e.inv ≫ f)
    refine ⟨η ≫ g, ?_⟩
    dsimp only
    dsimp only at hg
    rw [CategoryTheory.Functor.map_comp, hg]
    exact e.hom_inv_id_assoc f

/-- The normalized comparison with module maps, using the canonical single-object H0 iso. -/
def derivedNonpositiveHomToSingleEquiv (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] (M :
  ModuleCat.{u} R) :
    (X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≃
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X ⟶ M) :=
  (Equiv.ofBijective (fun f : X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f)
    (derivedNonpositiveHomologyZero_map_bijective (X := X) (Y := (DerivedCategory.singleFunctor
      (ModuleCat.{u} R) 0).obj M))).trans
    (Iso.homCongr (Iso.refl ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X))
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app M))

/-- The comparison uses the canonical H0 identification, with no chosen heart model. -/
@[simp] lemma derivedNonpositiveHomToSingleEquiv_apply
    (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] (M : ModuleCat.{u} R)
    (f : X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) :
    derivedNonpositiveHomToSingleEquiv X M f =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} R) 0).hom.app M := by
  simp only [derivedNonpositiveHomToSingleEquiv, Equiv.trans_apply,
    Equiv.ofBijective_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rfl

/-- The normalized comparison is natural in its nonpositive source. -/
lemma derivedNonpositiveHomToSingleEquiv_precomp
    {X Y : DerivedCategory (ModuleCat.{u} R)} [X.IsLE 0] [Y.IsLE 0] (M : ModuleCat.{u} R)
    (f : X ⟶ Y) (g : Y ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) :
    derivedNonpositiveHomToSingleEquiv X M (f ≫ g) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f ≫
        derivedNonpositiveHomToSingleEquiv Y M g := by
  simp only [derivedNonpositiveHomToSingleEquiv_apply,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- The canonical augmentation to the actual single object of H0. -/
def derivedNonpositiveAugmentation (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] :
    X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} R) 0).obj X) :=
  (derivedNonpositiveHomToSingleEquiv X ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
    X)).symm (𝟙 _)

/-- The augmentation induces the identity after the canonical H0 normalization. -/
@[simp] lemma derivedNonpositiveAugmentation_homology
    (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map (derivedNonpositiveAugmentation X) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X) = 𝟙 _ := by
  rw [← derivedNonpositiveHomToSingleEquiv_apply]
  exact (derivedNonpositiveHomToSingleEquiv X ((DerivedCategory.homologyFunctor (ModuleCat.{u} R)
    0).obj X)).apply_symm_apply (𝟙 _)

end SerrePositivity
