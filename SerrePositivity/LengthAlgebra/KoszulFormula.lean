module

public import SerrePositivity.LengthAlgebra.PerfectBaseChange
public import SerrePositivity.PerfectComplex.KoszulGeneration

/-! # Koszul Euler 数を係数とする基底公式

高次の Koszul 消滅や階数との一致を使わず、任意の Koszul Euler 数で比較する。
基底の Koszul 分解は明示的な仮定とする。
-/

@[expose] public section

universe u

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
