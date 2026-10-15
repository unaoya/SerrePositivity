module
public import SerrePositivity.DifferentialGraded.Complexes.TensorEnriched

/-! # chain条件を課さない次数0 cochainの右tensor

次数付き分裂を自由dg加群へ運ぶための成分API。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L T : Complex A}

def tensorGradedZeroComponent (r : Homogeneous K L 0) (P : Complex A) (n : ℤ) :
    (K ⊗ P).X n ⟶ (L ⊗ P).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j hij =>
    (r.v i i (add_zero i) ▷ P.X j) ≫ ιTensorObj L P i j n hij)

@[reassoc] lemma ι_tensorGradedZero (r : Homogeneous K L 0) (P : Complex A)
    (i j n : ℤ) (hij : i + j = n) :
    ιTensorObj K P i j n hij ≫ tensorGradedZeroComponent r P n =
      (r.v i i (add_zero i) ▷ P.X j) ≫ ιTensorObj L P i j n hij :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

lemma tensorGradedZeroComponent_ofHom (f : K ⟶ L) (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (Cochain.ofHom f) P n = (f ▷ P).f n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  rw [ι_tensorGradedZero, ι_whiskerRight, Cochain.ofHom_v]

lemma tensorGradedZeroComponent_add (r s : Homogeneous K L 0) (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (r + s) P n =
      tensorGradedZeroComponent r P n + tensorGradedZeroComponent s P n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  simp only [Preadditive.comp_add, ι_tensorGradedZero, Cochain.add_v,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

lemma tensorGradedZeroComponent_zero (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (0 : Homogeneous K L 0) P n = 0 := by
  apply mapBifunctor.hom_ext
  intro i j hij
  simp only [ι_tensorGradedZero, Cochain.zero_v,
    MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]

lemma tensorGradedZeroComponent_comp (r : Homogeneous K L 0) (s : Homogeneous L T 0)
    (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent r P n ≫ tensorGradedZeroComponent s P n =
      tensorGradedZeroComponent (r.comp s (zero_add 0)) P n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  rw [ι_tensorGradedZero_assoc, ι_tensorGradedZero]
  rw [ι_tensorGradedZero, Cochain.comp_zero_cochain_v]
  simp only [← Category.assoc, ← comp_whiskerRight]

lemma tensorGradedZeroComponent_id (P : Complex A) (n : ℤ) :
    tensorGradedZeroComponent (Cochain.ofHom (𝟙 K)) P n = 𝟙 _ := by
  rw [tensorGradedZeroComponent_ofHom, id_whiskerRight, HomologicalComplex.id_f]

lemma tensorGradedZeroComponent_apply (r : Homogeneous K L 0) (P : Complex A)
    (i j n : ℤ) (hij : i + j = n) (x : K.X i) (y : P.X j) :
    tensorGradedZeroComponent r P n (ιTensorObj K P i j n hij (x ⊗ₜ[A] y)) =
      ιTensorObj L P i j n hij (r.v i i (add_zero i) x ⊗ₜ[A] y) :=
  congrArg (fun a => a (x ⊗ₜ[A] y)) (ι_tensorGradedZero r P i j n hij)

/-- 左tensor作用は因子の次数0 cochainと可換する。chain条件は不要。 -/
lemma tensorGradedZeroComponent_naturality (r : Homogeneous K L 0) {P Q : Complex A}
    (p i j : ℤ) (hij : i + p = j) (a : Homogeneous P Q p) :
    ((tensorLeftHom K P Q).f p a).v i j hij ≫ tensorGradedZeroComponent r Q j =
      tensorGradedZeroComponent r P i ≫ ((tensorLeftHom L P Q).f p a).v i j hij := by
  apply mapBifunctor.hom_ext
  intro b c hbc
  change b + c = i at hbc
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change tensorGradedZeroComponent r Q j
    (((tensorLeftHom K P Q).f p a).v i j hij (ιTensorObj K P b c i hbc (x ⊗ₜ[A] y))) =
    ((tensorLeftHom L P Q).f p a).v i j hij
      (tensorGradedZeroComponent r P i (ιTensorObj K P b c i hbc (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply, tensorGradedZeroComponent_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorGradedZeroComponent_apply, tensorLeftHom_apply]
  rfl

end SerrePositivity.DifferentialGraded
