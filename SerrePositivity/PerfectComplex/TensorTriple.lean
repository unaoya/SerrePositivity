module

public import SerrePositivity.PerfectComplex.TensorHomogeneous

/-! # Signed rotations of three cochain tensor factors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

abbrev cochainTensorTripleι (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) :=
  (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
    ιTensorObj (cochainTensor P Q) T (i + j) k n h

lemma cochainTensorTriple_hom_ext (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {Y : ModuleCat.{u} R}
    {f g : (cochainTensor (cochainTensor P Q) T).X n ⟶ Y}
    (h : ∀ i j k (hijk : i + j + k = n),
      cochainTensorTripleι P Q T i j k n hijk ≫ f =
        cochainTensorTripleι P Q T i j k n hijk ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a k hak
  dsimp at hak
  apply cochainTensorX_whiskerRight_hom_ext P Q a (T.X k) Y
  intro i j hij
  subst a
  exact h i j k hak

lemma cochainTensorTripleι_apply (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      ιTensorObj (cochainTensor P Q) T (i + j) k n h
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R] z) := rfl

/-- Move the last factor to the front; the signed braiding is followed by reassociation. -/
def cochainTensorRotationIso (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor P Q) T ≅ cochainTensor (cochainTensor T P) Q :=
  cochainTensorSymmetry (cochainTensor P Q) T ≪≫ (cochainTensorAssociator T P Q).symm

lemma cochainTensorRotation_apply_ι
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorRotationIso P Q T).hom.f n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      ((i + j) * k).negOnePow •
        (cochainTensorTripleι T P Q k i j n (by omega) ((z ⊗ₜ[R] x) ⊗ₜ[R] y)) := by
  change (cochainTensorAssociator T P Q).inv.f n
    ((cochainTensorSymmetry (cochainTensor P Q) T).hom.f n
      (ιTensorObj (cochainTensor P Q) T (i + j) k n h
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R] z))) = _
  rw [cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorAssociator_inv_apply_ι_of_sum T P Q k i j (i + j) n rfl (by omega)]
  rfl

/-- Three right rotations return every factor and cancel the Koszul signs. -/
lemma cochainTensorRotation_cube (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorRotationIso P Q T).hom ≫ (cochainTensorRotationIso T P Q).hom ≫
      (cochainTensorRotationIso Q T P).hom = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P Q T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorRotationIso Q T P).hom.f n
    ((cochainTensorRotationIso T P Q).hom.f n
      ((cochainTensorRotationIso P Q T).hom.f n
        (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))) =
      cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)
  rw [cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorRotation_apply_ι]
  change ((i + j) * k).negOnePow • (((k + i) * j).negOnePow •
    (((j + k) * i).negOnePow •
      cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))) = _
  have hs : ((i + j) * k).negOnePow * ((k + i) * j).negOnePow *
      ((j + k) * i).negOnePow = 1 := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    have he : (i + j) * k + (k + i) * j + (j + k) * i =
        2 * (i * j + j * k + i * k) := by ring
    rw [he, Int.negOnePow_two_mul]
  rw [smul_smul, smul_smul, hs, one_smul]

abbrev cochainTensorTripleMap
    {P P' Q Q' T T' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (t : T ⟶ T') :=
  cochainTensorMap (cochainTensorMap f g) t

lemma cochainTensorTripleMap_apply_ι
    {P P' Q Q' T T' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (t : T ⟶ T')
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorTripleMap f g t).f n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      cochainTensorTripleι P' Q' T' i j k n h
        ((f.f i x ⊗ₜ[R] g.f j y) ⊗ₜ[R] t.f k z) := by
  rw [cochainTensorTripleι_apply, cochainTensorMap_apply_ι, cochainTensorMap_apply_ι]
  rfl

@[reassoc]
lemma cochainTensorRotation_naturality
    {P P' Q Q' T T' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (t : T ⟶ T') :
    cochainTensorTripleMap f g t ≫ (cochainTensorRotationIso P' Q' T').hom =
      (cochainTensorRotationIso P Q T).hom ≫ cochainTensorTripleMap t f g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P Q T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorRotationIso P' Q' T').hom.f n
    ((cochainTensorTripleMap f g t).f n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))) =
    (cochainTensorTripleMap t f g).f n
      ((cochainTensorRotationIso P Q T).hom.f n
        (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))
  rw [cochainTensorTripleMap_apply_ι, cochainTensorRotation_apply_ι,
    cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorTripleMap_apply_ι]

end SerrePositivity
