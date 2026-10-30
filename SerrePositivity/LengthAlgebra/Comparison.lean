module

public import SerrePositivity.LengthAlgebra.KoszulFormula
public import SerrePositivity.CategoryTheory.Euler

/-! # 二つの長さ付き代数による有限射影版の対称な比較

群は評価元の K₀ にのみ作用する。評価先の環・長さの同変性は要求しない。
共通定理 `homologicalEulerK0_pullback_conjSum_eq_of_base_formula` に、基底公式
`perfectBaseChangeEulerK0_eq_koszulEuler_mul` と係数変更の合成 `perfectBaseChangeEulerK0_comp` を入れる。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory IsLocalRing

variable {A S C D : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing S] [CommRing C] [CommRing D]
  (α : A →+* S) (φ : S →+* C) (ψ : S →+* D)
  {J : Ideal C} {I : Ideal D} (lam : NormalizedLength C J) (mu : NormalizedLength D I)
  (hfg : J.FG) (hIfg : I.FG) {e : ℕ} (z : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ α ∘ z))).radical)
  (hI : I ≤ (Ideal.span (Set.range (ψ ∘ α ∘ z))).radical)
  (hfin : KoszulFinite lam (φ ∘ α ∘ z)) (hfinD : KoszulFinite mu (ψ ∘ α ∘ z))
  (hz : Ideal.span (Set.range z) = maximalIdeal A) (hK : IsKoszulResolution z)

include hz hK in
/-- Koszul Euler 数の一致と K₀ の降下だけから、二つの評価の共役和は一致する。 -/
theorem perfectEuler_conjSum_eq
    {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G (TriangulatedK0 (SupportedPerfectHomotopy (α ∘ z)))]
    (hc : koszulEuler lam (φ ∘ α ∘ z) = koszulEuler mu (ψ ∘ α ∘ z))
    (hdesc : ∀ y : TriangulatedK0 (SupportedPerfectHomotopy (α ∘ z)),
      (∀ g : G, g • y = y) → ∃ (n : ℕ) (x : TriangulatedK0 (SupportedPerfectHomotopy z)),
        0 < n ∧ n • y = TriangulatedK0.map (supportedPerfectChangeRing α z) x)
    (y : TriangulatedK0 (SupportedPerfectHomotopy (α ∘ z))) :
    ∑ g : G, perfectBaseChangeEulerK0 φ lam hfg (α ∘ z) hJ hfin (g • y) =
      ∑ g : G, perfectBaseChangeEulerK0 ψ mu hIfg (α ∘ z) hI hfinD (g • y) := by
  -- 基底公式：係数変更の合成と、基底上の Koszul 生成による公式
  have hC := (perfectBaseChangeEulerK0_comp φ lam hfg α z hJ hfin).trans
    (perfectBaseChangeEulerK0_eq_koszulEuler_mul (φ.comp α) lam hfg z hJ hfin hz hK)
  have hD := (perfectBaseChangeEulerK0_comp ψ mu hIfg α z hI hfinD).trans
    (perfectBaseChangeEulerK0_eq_koszulEuler_mul (ψ.comp α) mu hIfg z hI hfinD hz hK)
  -- 共通定理の適用。評価は `C`、`D` 上の Euler 評価を係数変更で引き戻したもの
  exact homologicalEulerK0_pullback_conjSum_eq_of_base_formula _ _ _ _ _ _ _ _ _ _ _ _
    (TriangulatedK0.map (supportedPerfectChangeRing φ (α ∘ z)))
    (TriangulatedK0.map (supportedPerfectChangeRing ψ (α ∘ z)))
    (TriangulatedK0.map (supportedPerfectChangeRing α z))
    (fun x ↦ ordinaryBaseEulerK0 z hz (perfectToFreeK0 x))
    (koszulEuler lam (φ ∘ α ∘ z)) (koszulEuler mu (ψ ∘ α ∘ z))
    (fun x ↦ by
      have := DFunLike.congr_fun hC x
      simp only [perfectBaseChangeEulerK0, perfectEulerK0, RingHom.coe_comp, Function.comp_assoc,
        AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, smul_eq_mul] at this
      exact this)
    (fun x ↦ by
      have := DFunLike.congr_fun hD x
      simp only [perfectBaseChangeEulerK0, perfectEulerK0, RingHom.coe_comp, Function.comp_assoc,
        AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, smul_eq_mul] at this
      exact this)
    hc hdesc y

end SerrePositivity.LengthAlgebra
