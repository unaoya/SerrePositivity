module

public import Mathlib.LinearAlgebra.TensorProduct.Map

public import SerrePositivity.KST.Spectra.RationalTensorExtensionality

/-!
概要：単位に適合する有理テンソル表示は加法群の可換図式に対して自然。
方針：有理化された射をテンソル座標へ移し、a⊗1 上の計算で同定する。
規約：元の群と有理化の群の間の実際の準同型を入力とする。
使われ方：HA §1.4.2、BF 1978 §2。実際のスペクトルの射のテンソル表示。
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace SerrePositivity.KST.Spectra

variable {A : Type u} {B : Type v} {R : Type w} {S : Type z}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup R] [AddCommGroup S]

/-- 概要：単位に適合するテンソル表示の下で可換図式の有理化された射は元の射のテンソル。
方針：a⊗1 上の像を単位の可換式で計算し、一意性を使う。
規約：有理化された射に ℚ 線形性を追加仮定しない。
使われ方：HA §1.4.2、BF 1978 §2。有理化の自然な π_* 比較。 -/
theorem rationalTensor_realization_natural
    (eR : R ≃+ (A ⊗[ℤ] ℚ)) (eS : S ≃+ (B ⊗[ℤ] ℚ))
    (i : A →+ R) (j : B →+ S) (f : A →+ B) (g : R →+ S)
    (hi : ∀ a, eR (i a) = a ⊗ₜ[ℤ] (1 : ℚ))
    (hj : ∀ b, eS (j b) = b ⊗ₜ[ℤ] (1 : ℚ))
    (h : ∀ a, g (i a) = j (f a)) (r : R) :
    eS (g r) = (TensorProduct.map f.toIntLinearMap
      (LinearMap.id : ℚ →ₗ[ℤ] ℚ)) (eR r) := by
  let F := eS.toAddMonoidHom.comp (g.comp eR.symm.toAddMonoidHom)
  let T := (TensorProduct.map f.toIntLinearMap
    (LinearMap.id : ℚ →ₗ[ℤ] ℚ)).toAddMonoidHom
  have he : F = T := by
    apply rationalTensor_addHom_ext
    intro a
    have hx : eR.symm (a ⊗ₜ[ℤ] (1 : ℚ)) = i a := by
      apply eR.injective
      rw [eR.apply_symm_apply, hi]
    change eS (g (eR.symm (a ⊗ₜ[ℤ] (1 : ℚ)))) = T _
    rw [hx, h, hj]
    rfl
  have hr := DFunLike.congr_fun he (eR r)
  change eS (g (eR.symm (eR r))) = _ at hr
  simpa only [AddEquiv.symm_apply_apply, T, LinearMap.toAddMonoidHom_coe] using hr

/-- 概要：テンソル表示を持つ有理化群からの準同型は単位の像上で決まる。
方針：始域と終域をテンソル座標へ移し、a⊗1 上での一意性を適用する。
規約：始域の単位と表示の適合性だけを仮定する。
使われ方：HA §1.4.2。有理化の射の恒等・合成法則。 -/
theorem rationalTensor_realization_ext
    (eR : R ≃+ (A ⊗[ℤ] ℚ)) (eS : S ≃+ (B ⊗[ℤ] ℚ))
    (i : A →+ R) (hi : ∀ a, eR (i a) = a ⊗ₜ[ℤ] (1 : ℚ))
    (f g : R →+ S) (h : ∀ a, f (i a) = g (i a)) : f = g := by
  have he : eS.toAddMonoidHom.comp (f.comp eR.symm.toAddMonoidHom) =
      eS.toAddMonoidHom.comp (g.comp eR.symm.toAddMonoidHom) := by
    apply rationalTensor_addHom_ext
    intro a
    have hx : eR.symm (a ⊗ₜ[ℤ] (1 : ℚ)) = i a := by
      apply eR.injective
      rw [eR.apply_symm_apply, hi]
    change eS (f (eR.symm (a ⊗ₜ[ℤ] (1 : ℚ)))) = eS (g (eR.symm (a ⊗ₜ[ℤ] (1 : ℚ))))
    rw [hx, h]
  apply AddMonoidHom.ext
  intro r
  apply eS.injective
  have hr := DFunLike.congr_fun he (eR r)
  change eS (f (eR.symm (eR r))) = eS (g (eR.symm (eR r))) at hr
  simpa only [AddEquiv.symm_apply_apply] using hr

end SerrePositivity.KST.Spectra
