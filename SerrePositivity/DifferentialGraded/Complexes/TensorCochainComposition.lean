module
public import SerrePositivity.DifferentialGraded.Complexes.TensorEnriched

/-! # 左tensorによる全次数cochain合成の保存

豊穣合成の保存から通常順の斉次合成の保存を取り出す。
主モデルの豊穣合成に付く共通Koszul符号を単位スカラーの作用の単射性で消す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左tensorの全Hom写像は通常順のcochain合成も保存する。 -/
lemma tensorLeftHom_cochain_comp (K P Q T : Complex A) (p q m : ℤ) (hm : p + q = m)
    (f : Cochain P Q p) (g : Cochain Q T q) :
    (tensorLeftHom K P T).f m (f.comp g hm) =
      ((tensorLeftHom K P Q).f p f).comp ((tensorLeftHom K Q T).f q g) hm := by
  have h := congrArg (fun t : homComplex A P Q ⊗ homComplex A Q T ⟶
      homComplex A (K ⊗ P) (K ⊗ T) =>
    t.f m (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g)))
    (tensorLeftHom_comp K P Q T)
  change (tensorLeftHom K P T).f m
    ((enrichedComposition P Q T).f m
      (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g))) =
    (enrichedComposition _ _ _).f m
      ((tensorLeftHom K P Q ⊗ₘ tensorLeftHom K Q T).f m
        (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g))) at h
  rw [tensorMap_apply, enrichedComposition_apply, enrichedComposition_apply] at h
  simp only [Units.smul_def, map_zsmul] at h
  exact smul_left_cancel (p * q).negOnePow h

/-- 左tensorは二つのcochainの符号付き反交換式を保つ。 -/
lemma tensorLeftHom_cochain_anticommute (K P Q Q' T : Complex A)
    (p q m : ℤ) (hm : p + q = m) (hm' : q + p = m)
    (f : Cochain P Q p) (g : Cochain Q T q)
    (g' : Cochain P Q' q) (f' : Cochain Q' T p)
    (h : f.comp g hm = -(g'.comp f' hm')) :
    ((tensorLeftHom K P Q).f p f).comp ((tensorLeftHom K Q T).f q g) hm =
      -(((tensorLeftHom K P Q').f q g').comp ((tensorLeftHom K Q' T).f p f') hm') := by
  rw [← tensorLeftHom_cochain_comp, h, map_neg, tensorLeftHom_cochain_comp]

end SerrePositivity.DifferentialGraded
