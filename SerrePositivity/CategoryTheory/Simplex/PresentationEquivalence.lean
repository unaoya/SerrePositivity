module

public import SerrePositivity.CategoryTheory.Simplex.PresentationFaces
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-! # The presented simplex category is equivalent to the usual simplex category -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory SimplexCategoryGenRel

namespace SerrePositivity.SimplexPresentation

section SplitFactorization
universe v u
variable {C : Type u} [Category.{v} C] {X Y Z Z' : C}
  (e : X ⟶ Z) (m : Z ⟶ Y) (e' : X ⟶ Z') (m' : Z' ⟶ Y)
  [IsSplitEpi e] [IsSplitEpi e'] [Mono m] [Mono m'] (h : e ≫ m = e' ≫ m')

include h

omit [IsSplitEpi e'] [Mono m] [Mono m'] in
lemma splitFactor_hom_m : (section_ e ≫ e') ≫ m' = m := by
  rw [Category.assoc, ← h, ← Category.assoc, IsSplitEpi.id, Category.id_comp]

def splitFactorIso : Z ≅ Z' where
  hom := section_ e ≫ e'
  inv := section_ e' ≫ e
  hom_inv_id := by
    apply (cancel_mono m).mp
    rw [Category.assoc, splitFactor_hom_m e' m' e m h.symm,
      splitFactor_hom_m e m e' m' h, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono m').mp
    rw [Category.assoc, splitFactor_hom_m e m e' m' h,
      splitFactor_hom_m e' m' e m h.symm, Category.id_comp]
end SplitFactorization

lemma toSimplexCategory_map_injective {x y : SimplexCategoryGenRel} (f g : x ⟶ y)
    (h : toSimplexCategory.map f = toSimplexCategory.map g) : f = g := by
  obtain ⟨z, e, m, he, hm, rfl⟩ := exists_P_σ_P_δ_factorization f
  obtain ⟨z', e', m', he', hm', rfl⟩ := exists_P_σ_P_δ_factorization g
  have : IsSplitEpi (toSimplexCategory.map e) := isSplitEpi_toSimplexCategory_map_of_P_σ he
  have : IsSplitEpi (toSimplexCategory.map e') := isSplitEpi_toSimplexCategory_map_of_P_σ he'
  have : IsSplitMono (toSimplexCategory.map m) := isSplitMono_toSimplexCategory_map_of_P_δ hm
  have : IsSplitMono (toSimplexCategory.map m') := isSplitMono_toSimplexCategory_map_of_P_δ hm'
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  let i := splitFactorIso (toSimplexCategory.map e) (toSimplexCategory.map m)
    (toSimplexCategory.map e') (toSimplexCategory.map m') h
  have hz : z = z' := SimplexCategoryGenRel.ext (SimplexCategory.len_eq_of_isIso i.hom)
  subst z'
  have hi : i.hom = 𝟙 _ := SimplexCategory.eq_id_of_isIso i.hom
  have hmm : toSimplexCategory.map m' = toSimplexCategory.map m := by
    have hh := splitFactor_hom_m (toSimplexCategory.map e) (toSimplexCategory.map m)
      (toSimplexCategory.map e') (toSimplexCategory.map m') h
    change i.hom ≫ toSimplexCategory.map m' = toSimplexCategory.map m at hh
    simpa only [hi, Category.id_comp] using hh
  have hee : toSimplexCategory.map e = toSimplexCategory.map e' := by
    apply (cancel_mono (toSimplexCategory.map m)).mp
    simpa only [hmm] using h
  rw [map_injective_on_faces hm' hm hmm, map_injective_on_degeneracies he he' hee]

instance : toSimplexCategory.Faithful where
  map_injective := toSimplexCategory_map_injective _ _

def liftable : MorphismProperty SimplexCategory := fun {x y} f =>
  ∃ g : mk x.len ⟶ mk y.len, toSimplexCategory.map g = f

instance : liftable.IsMultiplicative where
  id_mem x := ⟨𝟙 _, CategoryTheory.Functor.map_id _ _⟩
  comp_mem f g hf hg := by
    obtain ⟨f', rfl⟩ := hf
    obtain ⟨g', rfl⟩ := hg
    exact ⟨f' ≫ g', CategoryTheory.Functor.map_comp _ _ _⟩

lemma liftable_eq_top : liftable = ⊤ :=
  SimplexCategory.morphismProperty_eq_top liftable
    (fun i => ⟨δ i, toSimplexCategory_map_δ i⟩)
    (fun i => ⟨σ i, toSimplexCategory_map_σ i⟩)

instance : toSimplexCategory.Full where
  map_surjective f := by
    have hf : liftable f := by rw [liftable_eq_top]; trivial
    exact hf

instance : toSimplexCategory.EssSurj where
  mem_essImage x := ⟨mk x.len, ⟨Iso.refl _⟩⟩

instance : toSimplexCategory.IsEquivalence where

/-- An inverse with definitionally fixed degree objects, for computing faces and degeneracies. -/
def inverse : SimplexCategory ⥤ SimplexCategoryGenRel where
  obj n := mk n.len
  map f := toSimplexCategory.preimage f
  map_id _ := toSimplexCategory.preimage_id
  map_comp {x y z} f g :=
    toSimplexCategory.preimage_comp (X := mk x.len) (Y := mk y.len) (Z := mk z.len) f g

@[simp] lemma inverse_obj (n : ℕ) : inverse.obj (SimplexCategory.mk n) = mk n := rfl

@[simp] lemma inverse_face {n : ℕ} (i : Fin (n + 2)) :
    inverse.map (SimplexCategory.δ i) = δ i := by
  apply toSimplexCategory.map_injective
  exact toSimplexCategory.map_preimage _

@[simp] lemma inverse_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    inverse.map (SimplexCategory.σ i) = σ i := by
  apply toSimplexCategory.map_injective
  exact toSimplexCategory.map_preimage _

lemma inverse_toSimplexCategory : inverse ⋙ toSimplexCategory = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change toSimplexCategory.map
    (toSimplexCategory.preimage (X := mk x.len) (Y := mk y.len) f) = f
  exact toSimplexCategory.map_preimage (X := mk x.len) (Y := mk y.len) f

lemma toSimplexCategory_inverse : toSimplexCategory ⋙ inverse = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change toSimplexCategory.preimage (toSimplexCategory.map f) = f
  exact toSimplexCategory.preimage_map f

def equivalence : SimplexCategoryGenRel ≌ SimplexCategory :=
  toSimplexCategory.asEquivalence

end SerrePositivity.SimplexPresentation
