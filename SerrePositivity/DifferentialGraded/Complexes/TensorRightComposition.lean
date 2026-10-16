module
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom

/-! # 右tensorの全次数合成と閉零chain mapとの整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorRightHom_apply_of_sum (K P Q : Complex A) (p i j a b n : ℤ)
    (ha : i + j = a) (hb : i + p = b) (hn : a + p = n)
    (f : Cochain P Q p) (x : P.X i) (y : K.X j) :
    ((tensorRightHom K P Q).f p f).v a n hn
      (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
    ιTensorObj Q K b j n (by omega) (f.v i b hb x ⊗ₜ[A] y) := by
  subst b
  exact tensorRightHom_apply K P Q p i j a n ha hn f x y

lemma tensorRightHom_cochain_comp (K P Q T : Complex A) (p q m : ℤ) (hm : p + q = m)
    (f : Cochain P Q p) (g : Cochain Q T q) :
    (tensorRightHom K P T).f m (f.comp g hm) =
      ((tensorRightHom K P Q).f p f).comp ((tensorRightHom K Q T).f q g) hm := by
  apply Cochain.ext
  intro a n hn
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorRightHom K P T).f m (f.comp g hm)).v a n hn
    (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
    (((tensorRightHom K P Q).f p f).comp
      ((tensorRightHom K Q T).f q g) hm).v a n hn
        (ιTensorObj P K i j a ha (x ⊗ₜ[A] y))
  rw [tensorRightHom_apply_of_sum K P T m i j a (i + p + q) n ha (by omega) hn,
    Cochain.comp_v _ _ hm i (i + p) (i + p + q) rfl rfl,
    Cochain.comp_v _ _ hm a (a + p) n rfl (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [tensorRightHom_apply, tensorRightHom_apply]

lemma tensorRightHom_ofHom (K P Q : Complex A) (f : P ⟶ Q) :
    (tensorRightHom K P Q).f 0 (Cochain.ofHom f) = Cochain.ofHom (f ▷ K) := by
  apply Cochain.ext₀
  intro a
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorRightHom K P Q).f 0 (Cochain.ofHom f)).v a a (add_zero a)
    (ιTensorObj P K i j a ha (x ⊗ₜ[A] y)) =
      (f ▷ K).f a (ιTensorObj P K i j a ha (x ⊗ₜ[A] y))
  rw [tensorRightHom_apply_of_sum K P Q 0 i j a i a ha (add_zero i) (add_zero a),
    whiskerRight_apply, Cochain.ofHom_v]

end SerrePositivity.DifferentialGraded
