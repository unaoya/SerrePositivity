module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeSquare
/-! 二つの鎖写像の直和の cone を、左右の cone の直和へ分解する実鎖同型。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (f : P ⟶ Q) (g : S ⟶ T)

lemma dgGluingConeMap_add {A B : Complex R} (a : A ⟶ B)
    (x x' : P ⟶ A) (y y' : Q ⟶ B)
    (h : f ≫ y = x ≫ a) (h' : f ≫ y' = x' ≫ a)
    (hh : f ≫ (y + y') = (x + x') ≫ a) :
    mappingCone.map f a (x + x') (y + y') hh =
      mappingCone.map f a x y h + mappingCone.map f a x' y' h' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp only [mappingCone.map, mappingCone.inl_v_desc_f, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.add_f_apply, Preadditive.comp_add,
      Preadditive.add_comp]
  · simp only [mappingCone.map, mappingCone.inr_f_desc_f, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f, Preadditive.comp_add, Preadditive.add_comp]

lemma dgGluingConeMap_zero {A B : Complex R} (a : A ⟶ B)
    (h : f ≫ (0 : Q ⟶ B) = (0 : P ⟶ A) ≫ a) :
    mappingCone.map f a 0 0 h = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp [mappingCone.map]
  · simp [mappingCone.map]

def dgGluingConeLeftProjection : mappingCone (biprod.map f g) ⟶ mappingCone f :=
  mappingCone.map _ _ biprod.fst biprod.fst (by simp)
def dgGluingConeRightProjection : mappingCone (biprod.map f g) ⟶ mappingCone g :=
  mappingCone.map _ _ biprod.snd biprod.snd (by simp)
def dgGluingConeLeftInclusion : mappingCone f ⟶ mappingCone (biprod.map f g) :=
  mappingCone.map _ _ biprod.inl biprod.inl (by simp)
def dgGluingConeRightInclusion : mappingCone g ⟶ mappingCone (biprod.map f g) :=
  mappingCone.map _ _ biprod.inr biprod.inr (by simp)

lemma dgGluingConeInclusion_projection_left :
    dgGluingConeLeftInclusion f g ≫ dgGluingConeLeftProjection f g = 𝟙 _ := by
  rw [dgGluingConeLeftInclusion, dgGluingConeLeftProjection, ← mappingCone.map_comp]
  simp only [biprod.inl_fst]
  exact mappingCone.map_id f

lemma dgGluingConeInclusion_projection_right :
    dgGluingConeRightInclusion f g ≫ dgGluingConeRightProjection f g = 𝟙 _ := by
  rw [dgGluingConeRightInclusion, dgGluingConeRightProjection, ← mappingCone.map_comp]
  simp only [biprod.inr_snd]
  exact mappingCone.map_id g

lemma dgGluingConeInclusion_projection_left_right :
    dgGluingConeLeftInclusion f g ≫ dgGluingConeRightProjection f g = 0 := by
  rw [dgGluingConeLeftInclusion, dgGluingConeRightProjection, ← mappingCone.map_comp]
  simp only [biprod.inl_snd]
  exact dgGluingConeMap_zero f g _

lemma dgGluingConeInclusion_projection_right_left :
    dgGluingConeRightInclusion f g ≫ dgGluingConeLeftProjection f g = 0 := by
  rw [dgGluingConeRightInclusion, dgGluingConeLeftProjection, ← mappingCone.map_comp]
  simp only [biprod.inr_fst]
  exact dgGluingConeMap_zero g f _

lemma dgGluingConeProjection_inclusion_total :
    dgGluingConeLeftProjection f g ≫ dgGluingConeLeftInclusion f g +
      dgGluingConeRightProjection f g ≫ dgGluingConeRightInclusion f g = 𝟙 _ := by
  rw [dgGluingConeLeftProjection, dgGluingConeLeftInclusion,
    dgGluingConeRightProjection, dgGluingConeRightInclusion,
    ← mappingCone.map_comp, ← mappingCone.map_comp,
    ← dgGluingConeMap_add _ _ _ _ _ _ _ _ (by simp)]
  simp only [biprod.total]
  exact mappingCone.map_id _

def dgGluingConeBiproductIso : mappingCone (biprod.map f g) ≅ mappingCone f ⊞ mappingCone g where
  hom := biprod.lift (dgGluingConeLeftProjection f g) (dgGluingConeRightProjection f g)
  inv := biprod.desc (dgGluingConeLeftInclusion f g) (dgGluingConeRightInclusion f g)
  hom_inv_id := by
    rw [biprod.lift_desc]
    exact dgGluingConeProjection_inclusion_total f g
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [dgGluingConeInclusion_projection_left, dgGluingConeInclusion_projection_right,
        dgGluingConeInclusion_projection_left_right, dgGluingConeInclusion_projection_right_left]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
