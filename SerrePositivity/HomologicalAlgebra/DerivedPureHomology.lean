module
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Natural normalized comparison of pure derived objects with their actual homology -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A pure object has a single-object comparison inducing the identity on its actual homology. -/
lemma exists_normalizedPureHomologyIso (X : DerivedCategory C) (i : ℤ)
    [X.IsGE i] [X.IsLE i] :
    ∃ e : X ≅ (DerivedCategory.singleFunctor C i).obj
        ((DerivedCategory.homologyFunctor C i).obj X),
      (DerivedCategory.homologyFunctor C i).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app
          ((DerivedCategory.homologyFunctor C i).obj X) = 𝟙 _ := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X i
  let h := (DerivedCategory.homologyFunctor C i).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app M
  refine ⟨e ≪≫ (DerivedCategory.singleFunctor C i).mapIso h.symm, ?_⟩
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.naturality h.inv
  change (DerivedCategory.homologyFunctor C i).map
    ((DerivedCategory.singleFunctor C i).map h.inv) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app _ =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app M ≫ h.inv at hn
  rw [hn]
  change (DerivedCategory.homologyFunctor C i).map e.hom ≫
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app M ≫ h.inv) = _
  rw [← Category.assoc]
  exact h.hom_inv_id

/-- Choose a pure-object comparison normalized by the identity on actual homology. -/
def normalizedPureHomologyIso (X : DerivedCategory C) (i : ℤ) [X.IsGE i] [X.IsLE i] :
    X ≅ (DerivedCategory.singleFunctor C i).obj
      ((DerivedCategory.homologyFunctor C i).obj X) :=
  (exists_normalizedPureHomologyIso X i).choose

lemma normalizedPureHomologyIso_homology (X : DerivedCategory C) (i : ℤ)
    [X.IsGE i] [X.IsLE i] :
    (DerivedCategory.homologyFunctor C i).map (normalizedPureHomologyIso X i).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app
        ((DerivedCategory.homologyFunctor C i).obj X) = 𝟙 _ :=
  (exists_normalizedPureHomologyIso X i).choose_spec

/-- On objects concentrated in one degree, homology detects equality of derived morphisms. -/
lemma pureHomology_map_injective (i : ℤ) {X Y : DerivedCategory C}
    [X.IsGE i] [X.IsLE i] [Y.IsGE i] [Y.IsLE i] {f g : X ⟶ Y}
    (h : (DerivedCategory.homologyFunctor C i).map f =
      (DerivedCategory.homologyFunctor C i).map g) : f = g := by
  let eX := normalizedPureHomologyIso X i
  let eY := normalizedPureHomologyIso Y i
  let A := DerivedCategory.singleFunctor C i
  let H := DerivedCategory.homologyFunctor C i
  have : (A ⋙ H).Faithful := Functor.Faithful.of_iso
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).symm
  obtain ⟨f', hf'⟩ := A.map_surjective (eX.inv ≫ f ≫ eY.hom)
  obtain ⟨g', hg'⟩ := A.map_surjective (eX.inv ≫ g ≫ eY.hom)
  change H.map f = H.map g at h
  have h' : (A ⋙ H).map f' = (A ⋙ H).map g' := by
    simp only [Functor.comp_map, hf', hg', Functor.map_comp, h]
  have he := (A ⋙ H).map_injective h'
  rw [he] at hf'
  rw [hg'] at hf'
  exact (cancel_mono eY.hom).mp ((cancel_epi eX.inv).mp hf'.symm)

/-- Normalization makes the chosen pure-object comparisons natural in every derived morphism. -/
lemma normalizedPureHomologyIso_naturality (i : ℤ) {X Y : DerivedCategory C}
    [X.IsGE i] [X.IsLE i] [Y.IsGE i] [Y.IsLE i] (f : X ⟶ Y) :
    f ≫ (normalizedPureHomologyIso Y i).hom =
      (normalizedPureHomologyIso X i).hom ≫
        (DerivedCategory.singleFunctor C i).map ((DerivedCategory.homologyFunctor C i).map f) := by
  apply pureHomology_map_injective i
  apply (cancel_mono ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app
    ((DerivedCategory.homologyFunctor C i).obj Y))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [normalizedPureHomologyIso_homology, Category.comp_id]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.naturality
    ((DerivedCategory.homologyFunctor C i).map f)
  change (DerivedCategory.homologyFunctor C i).map
    ((DerivedCategory.singleFunctor C i).map ((DerivedCategory.homologyFunctor C i).map f)) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app _ =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app _ ≫
          (DerivedCategory.homologyFunctor C i).map f at hn
  rw [hn, ← Category.assoc, normalizedPureHomologyIso_homology, Category.id_comp]

/-- The identity normalization uniquely determines the pure-object comparison. -/
lemma normalizedPureHomologyIso_unique (X : DerivedCategory C) (i : ℤ)
    [X.IsGE i] [X.IsLE i]
    (e : X ≅ (DerivedCategory.singleFunctor C i).obj
      ((DerivedCategory.homologyFunctor C i).obj X))
    (he : (DerivedCategory.homologyFunctor C i).map e.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app
        ((DerivedCategory.homologyFunctor C i).obj X) = 𝟙 _) :
    e = normalizedPureHomologyIso X i := by
  apply Iso.ext
  apply pureHomology_map_injective i
  apply (cancel_mono ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app
    ((DerivedCategory.homologyFunctor C i).obj X))).mp
  rw [he, normalizedPureHomologyIso_homology]

end SerrePositivity
