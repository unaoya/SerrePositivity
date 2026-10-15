module
public import SerrePositivity.DifferentialGraded.Complexes.Shift
public import SerrePositivity.HomologicalAlgebra.CochainTensorShift

/-! # 左tensor因子のshift比較と全斉次Hom

通常のsign-freeな左shift比較が、dg作用のshift符号とも整合することを証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorShiftLeft_apply (K P : Complex A) (s b c n : ℤ) (hbc : b + c = n)
    (x : (K⟦s⟧).X b) (y : P.X c) :
    (SerrePositivity.cochainTensorShiftLeft K P s).hom.f n
      (ιTensorObj (K⟦s⟧) P b c n hbc (x ⊗ₜ[A] y)) =
      ιTensorObj K P (b + s) c (n + s) (by omega) (x ⊗ₜ[A] y) := by
  have h := congrArg (fun f => f (x ⊗ₜ[A] y))
    (SerrePositivity.ιTensorObj_cochainTensorShiftLeft K P s b c n hbc)
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id] at h
  change (SerrePositivity.cochainTensorShiftLeft K P s).hom.f n
      (ιTensorObj (K⟦s⟧) P b c n hbc (x ⊗ₜ[A] y)) =
    (𝟙 (K.X (b + s)) ▷ P.X c ≫
      ιTensorObj K P (b + s) c (n + s) (by omega)) (x ⊗ₜ[A] y) at h
  rw [id_whiskerRight, Category.id_comp] at h
  exact h

/-- tensor–shift比較の全次数dg自然性。 -/
lemma tensorShiftLeft_hom_naturality (K P Q : Complex A) (s : ℤ) :
    tensorLeftHom (K⟦s⟧) P Q ≫
      homPostcompose ((K⟦s⟧) ⊗ P) (SerrePositivity.cochainTensorShiftLeft K Q s).hom =
    tensorLeftHom K P Q ≫ shiftHom s (K ⊗ P) (K ⊗ Q) ≫
      homPrecompose (SerrePositivity.cochainTensorShiftLeft K P s).hom ((K ⊗ Q)⟦s⟧) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Cochain.ext
  intro i j hij
  change (((tensorLeftHom (K⟦s⟧) P Q).f p a).comp
      (Cochain.ofHom (SerrePositivity.cochainTensorShiftLeft K Q s).hom) (add_zero p)).v i j hij =
    ((Cochain.ofHom (SerrePositivity.cochainTensorShiftLeft K P s).hom).comp
      ((shiftHom s (K ⊗ P) (K ⊗ Q)).f p ((tensorLeftHom K P Q).f p a)) (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v]
  apply mapBifunctor.hom_ext
  intro b c hbc
  change b + c = i at hbc
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (SerrePositivity.cochainTensorShiftLeft K Q s).hom.f j
      (((tensorLeftHom (K⟦s⟧) P Q).f p a).v i j hij
        (ιTensorObj (K⟦s⟧) P b c i hbc (x ⊗ₜ[A] y))) =
    (((shiftHom s (K ⊗ P) (K ⊗ Q)).f p ((tensorLeftHom K P Q).f p a)).v i j hij)
      ((SerrePositivity.cochainTensorShiftLeft K P s).hom.f i
        (ιTensorObj (K⟦s⟧) P b c i hbc (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorShiftLeft_apply, tensorShiftLeft_apply, shiftHom_v]
  change (p * b).negOnePow • _ = (s * p).negOnePow •
    (((tensorLeftHom K P Q).f p a).v (i + s) (j + s) (by omega)
      (ιTensorObj K P (b + s) c (i + s) (by omega) (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply, smul_smul]
  have hs : (s * p).negOnePow * (p * (b + s)).negOnePow = (p * b).negOnePow := by
    rw [mul_add, Int.negOnePow_add, mul_comm p s, mul_left_comm,
      Int.units_mul_self, mul_one]
  rw [hs]

end SerrePositivity.DifferentialGraded
