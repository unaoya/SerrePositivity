module
public import SerrePositivity.DifferentialGraded.Complexes.Braiding
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # tensorの左因子を横切るパラメータ複体 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- KをPの右側へ移す。符号はKとPの次数の積。 -/
def parameterCross (K P Q : Complex A) : K ⊗ (P ⊗ Q) ⟶ P ⊗ (K ⊗ Q) :=
  (α_ K P Q).inv ≫ (signedSwap K P).hom ▷ Q ≫ (α_ P K Q).hom

@[reassoc]
lemma parameterCross_naturality_left (K : Complex A) {P P' : Complex A}
    (f : P ⟶ P') (Q : Complex A) :
    (K ◁ (f ▷ Q)) ≫ parameterCross K P' Q =
      parameterCross K P Q ≫ (f ▷ (K ⊗ Q)) := by
  have h := signedSwap_naturality (𝟙 K) f
  simp only [id_tensorHom, tensorHom_id] at h
  unfold parameterCross
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, h,
    comp_whiskerRight, Category.assoc, associator_naturality_left]
  simp only [Category.assoc]

@[reassoc]
lemma parameterCross_naturality_right (K P : Complex A) {Q Q' : Complex A}
    (g : Q ⟶ Q') :
    (K ◁ (P ◁ g)) ≫ parameterCross K P Q' =
      parameterCross K P Q ≫ (P ◁ (K ◁ g)) := by
  unfold parameterCross
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]
  simp only [Category.assoc]

/-- KをP⊗Qの右へ動かすことはP、Qの順に動かすことに等しい。 -/
@[reassoc]
lemma parameterCross_tensor (K P Q T : Complex A) :
    parameterCross K (P ⊗ Q) T ≫ (α_ P Q (K ⊗ T)).hom =
    (K ◁ (α_ P Q T).hom) ≫ parameterCross K P (Q ⊗ T) ≫
      (P ◁ parameterCross K Q T) := by
  unfold parameterCross signedSwap
  simp only [← braiding_eq_existing]
  rw [BraidedCategory.braiding_tensor_right_hom]
  monoidal

/-- パラメータと第一因子の次数の積だけが交換符号に現れる。 -/
lemma parameterCross_apply (K P Q : Complex A) (k r s n : ℤ) (hn : k + (r + s) = n)
    (t : K.X k) (m : P.X r) (v : Q.X s) :
    (parameterCross K P Q).f n
      (ιTensorObj K (P ⊗ Q) k (r + s) n hn
        (t ⊗ₜ[A] ιTensorObj P Q r s (r + s) rfl (m ⊗ₜ[A] v))) =
    (k * r).negOnePow • ιTensorObj P (K ⊗ Q) r (k + s) n (by omega)
      (m ⊗ₜ[A] ιTensorObj K Q k s (k + s) rfl (t ⊗ₜ[A] v)) := by
  change (α_ P K Q).hom.f n
    (((signedSwap K P).hom ▷ Q).f n
      ((α_ K P Q).inv.f n
        (ιTensorObj K (P ⊗ Q) k (r + s) n hn
          (t ⊗ₜ[A] ιTensorObj P Q r s (r + s) rfl (m ⊗ₜ[A] v))))) = _
  rw [associator_inv_apply, whiskerRight_apply, signedSwap_apply]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
  rw [associator_apply_of_sum]

end SerrePositivity.DifferentialGraded
