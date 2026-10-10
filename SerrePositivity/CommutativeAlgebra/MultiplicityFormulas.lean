module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.Inputs.RegularLocalRing

/-!
# パラメータイデアルの重複度公式

§2.5 の共通部分で使う二つの標準的な重複度の入力を明示する。
成分ごとの冪の公式と、Koszul の Euler 特性との同定は未証明。
正則基底上の階数公式は、後者と既存の `koszulEulerChar_eq_finrank` から導く。
未証明入力を構造体にまとめず、それぞれの主張を証明中で直接使用する。
-/

public section
universe u
open IsLocalRing
namespace SerrePositivity.HilbertSamuel

/-- パラメータ系の成分ごとの冪に対する重複度公式。
`(z₁^v,…,z_h^v)` はイデアル `(z₁,…,z_h)^v` とは異なる。
標準的な重複度理論の未証明入力であり、定理2.5固有の仮定ではない。 -/
theorem multiplicity_parameter_pow (D : Type u) [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (v : ℕ) (hv : 0 < v) :
    multiplicity D (Ideal.span (Set.range fun i ↦ z i ^ v)) D =
      (v : ℚ) ^ h * multiplicity D (Ideal.span (Set.range z)) D := by
  sorry

/-- Koszul の Euler 特性と重複度の一致を、有限な局所環拡大に沿って係数制限した形。
Koszul の重複度公式（Stacks 0AZZ）と、剰余体が一致する場合の長さの一致が必要。
この橋渡しは未証明であり、正則基底での Euler 特性の既存証明とは区別する。 -/
theorem multiplicity_eq_koszulEulerChar_of_residue_surjective
    (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (multiplicity D (Ideal.span (Set.range (algebraMap A D ∘ t))) D : ℝ) =
      koszulEulerChar A D t := by
  sorry

/-- 正則基底のパラメータに対する重複度は、剰余体が一致すれば基底上の階数に等しい。
未証明の重複度との橋渡しと、既存の Euler 特性の階数公式からの導出。 -/
theorem multiplicity_eq_rank_of_regular_base
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdim : ringKrullDim A = h) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (multiplicity D (Ideal.span (Set.range (algebraMap A D ∘ t))) D : ℝ) =
      Module.finrank A D := by
  rw [multiplicity_eq_koszulEulerChar_of_residue_surjective A D hinj hres t hsop,
    koszulEulerChar_eq_finrank A D t ht hdim]

end SerrePositivity.HilbertSamuel
