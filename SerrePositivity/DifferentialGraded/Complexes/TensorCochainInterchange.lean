module
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom

/-! # 全次数cochainの左右tensorの交差符号

異なる二つのtensor因子に作用するcochainの順序交換は、次数積のKoszul符号を持つ。
ε消去と後方のcochainの交換にも使用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左因子と右因子へのcochain作用を交換する際の符号は(-1)^(pq)。 -/
lemma tensorCochain_interchange (P P' Q Q' : Complex A) (p q m : ℤ)
    (hm : p + q = m) (hm' : q + p = m) (f : Cochain P P' p) (g : Cochain Q Q' q) :
    ((tensorRightHom Q P P').f p f).comp ((tensorLeftHom P' Q Q').f q g) hm =
      (p * q).negOnePow • (((tensorLeftHom P Q Q').f q g).comp
        ((tensorRightHom Q' P P').f p f) hm') := by
  apply Cochain.ext
  intro a n hn
  rw [Units.smul_def, Cochain.smul_v]
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rw [Cochain.comp_v _ _ hm a (a + p) n rfl (by omega)]
  change ((tensorLeftHom P' Q Q').f q g).v (a + p) n (by omega)
    (((tensorRightHom Q P P').f p f).v a (a + p) rfl
      (ιTensorObj P Q i j a ha (x ⊗ₜ[A] y))) =
    (p * q).negOnePow •
      ((((tensorLeftHom P Q Q').f q g).comp
        ((tensorRightHom Q' P P').f p f) hm').v a n hn
          (ιTensorObj P Q i j a ha (x ⊗ₜ[A] y)))
  rw [tensorRightHom_apply,
    tensorLeftHom_apply_of_sum P' Q Q' q (i + p) j (a + p) (j + q) n
      (by omega) rfl (by omega)]
  rw [Cochain.comp_v _ _ hm' a (a + q) n rfl (by omega)]
  change (q * (i + p)).negOnePow •
      ιTensorObj P' Q' (i + p) (j + q) n (by omega)
        (f.v i (i + p) rfl x ⊗ₜ[A] g.v j (j + q) rfl y) =
    (p * q).negOnePow • ((tensorRightHom Q' P P').f p f).v (a + q) n (by omega)
      (((tensorLeftHom P Q Q').f q g).v a (a + q) rfl
        (ιTensorObj P Q i j a ha (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply_of_sum P Q Q' q i j a (j + q) (a + q) ha rfl rfl,
    cochain_v_units_smul, tensorRightHom_apply, smul_smul, ← Int.negOnePow_add]
  congr 2
  ring

/-- 次数1同士の異なる因子への作用は反交換する。 -/
lemma tensorCochain_odd_anticommute (P P' Q Q' : Complex A)
    (f : Cochain P P' 1) (g : Cochain Q Q' 1) :
    ((tensorRightHom Q P P').f 1 f).comp ((tensorLeftHom P' Q Q').f 1 g)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom P Q Q').f 1 g).comp ((tensorRightHom Q' P P').f 1 f)
      (show (1 : ℤ) + 1 = 2 by omega)) := by
  simpa [Units.smul_def] using
    tensorCochain_interchange P P' Q Q' 1 1 2 (by omega) (by omega) f g

end SerrePositivity.DifferentialGraded
