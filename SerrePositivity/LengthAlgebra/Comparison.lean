module

public import SerrePositivity.LengthAlgebra.KoszulFormula
public import SerrePositivity.CategoryTheory.EulerComparison

/-! # 二つの長さ付き代数による有限射影版の対称な比較

群は評価元の K₀ にのみ作用する。評価先の環・長さの同変性は要求しない。
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
  apply conjSum_eq (TriangulatedK0.map (supportedPerfectChangeRing α z)) _ _ _ hdesc y
  intro x
  change ((perfectBaseChangeEulerK0 φ lam hfg (α ∘ z) hJ hfin).comp
    (TriangulatedK0.map (supportedPerfectChangeRing α z))) x =
      ((perfectBaseChangeEulerK0 ψ mu hIfg (α ∘ z) hI hfinD).comp
        (TriangulatedK0.map (supportedPerfectChangeRing α z))) x
  rw [perfectBaseChangeEulerK0_comp, perfectBaseChangeEulerK0_comp,
    perfectBaseChangeEulerK0_eq_koszulEuler_mul (φ.comp α) lam hfg z hJ hfin hz hK,
    perfectBaseChangeEulerK0_eq_koszulEuler_mul (ψ.comp α) mu hIfg z hI hfinD hz hK]
  change ((koszulEuler lam (φ ∘ α ∘ z) • ordinaryBaseEulerK0 z hz).comp perfectToFreeK0) x =
    ((koszulEuler mu (ψ ∘ α ∘ z) • ordinaryBaseEulerK0 z hz).comp perfectToFreeK0) x
  rw [hc]

end SerrePositivity.LengthAlgebra
