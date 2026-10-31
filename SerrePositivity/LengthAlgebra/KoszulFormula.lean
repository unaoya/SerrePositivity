module

public import SerrePositivity.LengthAlgebra.Perfect
public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.CategoryTheory.Euler

/-! # Koszul Euler 数による基底公式と対称な比較

## 概要

任意の Koszul Euler 数を係数とする基底公式（高次の Koszul 消滅や階数との一致を使わない）を示し、二つの長さ付き代数による有限射影版の対称な比較を与える。

## 方針

共通定理 `homologicalEulerK0_pullback_orbitSum_eq_of_base_formula`（CategoryTheory/Euler）に、基底公式と係数変更の合成を入れる。群は評価元の K₀ にのみ作用する。

## 規約

基底の Koszul 分解は明示的な仮定とする。評価先の環・長さの同変性は要求しない。

## 使われ方

Paper の Lemma 3.5 と §4。
-/

@[expose] public noncomputable section

universe u

section KoszulFormulaPart

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits IsLocalRing

variable {A C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing C] (φ : A →+* C) {J : Ideal C} (lam : NormalizedLength C J)
  (hfg : J.FG) {e : ℕ} (z : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : KoszulFinite lam (φ ∘ z))
  (hz : Ideal.span (Set.range z) = maximalIdeal A) (hK : IsKoszulResolution z)

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- Koszul 生成元での Euler 評価。 -/
lemma freeBaseChangeEulerK0_koszul :
    freeBaseChangeEulerK0 φ lam hfg z hJ hfin (K0.mk (koszulPerfSupp z)) =
      koszulEuler lam (φ ∘ z) := by
  rw [freeBaseChangeEulerK0_mk]
  exact lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso (baseChangeKoszulIso φ z))

/-- 基底の通常 Euler 評価。Koszul 生成の正規化に用いる。 -/
noncomputable def ordinaryBaseEulerK0 : K0Supported A z →+ ℝ := by
  let := isArtinianRing_quotient_span_of_eq hz
  exact chiOrdHom z

include hK in
/-- 有限自由モデル上の基底公式。係数は任意の実数値の Koszul Euler 数である。 -/
theorem freeBaseChangeEulerK0_eq_koszulEuler_mul :
    freeBaseChangeEulerK0 φ lam hfg z hJ hfin =
      koszulEuler lam (φ ∘ z) • ordinaryBaseEulerK0 z hz := by
  let := isArtinianRing_quotient_span_of_eq hz
  dsimp only [ordinaryBaseEulerK0]
  apply K0.hom_ext_koszul hz hK
  rw [freeBaseChangeEulerK0_koszul, AddMonoidHom.smul_apply, chiOrdHom_mk]
  change koszulEuler lam (φ ∘ z) = koszulEuler lam (φ ∘ z) * chiOrd (koszulComplex z)
  rw [chiOrd_koszulComplex hK hz, mul_one]

include hK in
/-- 有限射影版の K₀ 上の基底公式。局所環での比較同型を使う。 -/
theorem perfectBaseChangeEulerK0_eq_koszulEuler_mul :
    perfectBaseChangeEulerK0 φ lam hfg z hJ hfin =
      (koszulEuler lam (φ ∘ z) • ordinaryBaseEulerK0 z hz).comp perfectToFreeK0 := by
  have h := congrArg (fun f : K0Supported A z →+ ℝ ↦ f.comp perfectToFreeK0)
    (freeBaseChangeEulerK0_eq_koszulEuler_mul φ lam hfg z hJ hfin hz hK)
  simpa only [freeBaseChangeEulerK0, AddMonoidHom.comp_assoc,
    freeToPerfectK0_comp_perfectToFreeK0, AddMonoidHom.comp_id] using h

include hfg hJ hfin hz hK in
/-- 個々の複体での基底公式。高次消滅は仮定しない。 -/
theorem lambdaEuler_baseChange_eq_koszulEuler_mul
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : IsPerfectSupported z P) :
    lambdaEuler lam (baseChange φ P) = koszulEuler lam (φ ∘ z) * chiOrd P := by
  have h := DFunLike.congr_fun
    (freeBaseChangeEulerK0_eq_koszulEuler_mul φ lam hfg z hJ hfin hz hK) (K0.mk ⟨P, hP⟩)
  simpa only [freeBaseChangeEulerK0_mk, ordinaryBaseEulerK0, AddMonoidHom.smul_apply,
    chiOrdHom_mk, smul_eq_mul, chiLam, lambdaEuler]
    using h

end SerrePositivity.LengthAlgebra

end KoszulFormulaPart

section ComparisonPart

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

end ComparisonPart
