module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.Inputs.RegularLocalRing

/-!
# パラメータイデアルの重複度公式

§2.5 の共通部分で使う二つの標準的な重複度の入力を明示する。
成分ごとの冪の公式と、同じ環上での Koszul 重複度公式は未証明。
剰余体が一致する拡大に沿う係数制限の部分は、各ホモロジーの長さの一致から証明する。
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

set_option backward.isDefEq.respectTransparency false in
/-- 同じ環の上で測った Koszul Euler 数は、通常の複体の Euler 数である。 -/
lemma koszulEulerChar_self (D : Type u) [CommRing D] {r : ℕ} (z : Fin r → D) :
    koszulEulerChar D D z = chiOrd (koszulComplex z) := by
  unfold koszulEulerChar chiOrd
  congr 1

/-- 剰余体への全射があれば、Koszul Euler 数の係数制限は値を変えない。
有限性・単射性・パラメータ条件は、この長さの比較自体には不要。 -/
theorem koszulEulerChar_eq_chiOrd_of_residue_surjective
    (A D : Type u) [CommRing A] [CommRing D] [IsLocalRing D] [Algebra A D]
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) :
    koszulEulerChar A D t = chiOrd (koszulComplex (algebraMap A D ∘ t)) := by
  unfold koszulEulerChar chiOrd
  congr 1
  funext i
  rw [length_restrictScalars_eq hres]

/-- **未証明の標準可換環論：Koszul 重複度公式。**
パラメータ系の Hilbert–Samuel 重複度は、同じ環上の Koszul Euler 数に等しい。
Stacks Project, Tag 0AZZ（Theorem 43.15.5、係数加群 `M = D`）。
https://stacks.math.columbia.edu/tag/0AZZ
旧 `multiplicity_eq_koszulEulerChar_of_residue_surjective` に含まれていた未証明箇所を
この固有の主張に限定した。係数制限の議論は次の定理で証明する。 -/
theorem multiplicity_eq_chiOrd_koszul
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    (multiplicity D (Ideal.span (Set.range z)) D : ℝ) = chiOrd (koszulComplex z) := by
  sorry

/-- Koszul 重複度公式を、剰余体が一致する有限局所環拡大に沿って係数制限する。
未証明なのは前掲の同一環上の公式だけであり、長さの移送は証明済み。 -/
theorem multiplicity_eq_koszulEulerChar_of_residue_surjective
    (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    (_hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (multiplicity D (Ideal.span (Set.range (algebraMap A D ∘ t))) D : ℝ) =
      koszulEulerChar A D t := by
  rw [koszulEulerChar_eq_chiOrd_of_residue_surjective A D hres t]
  exact multiplicity_eq_chiOrd_koszul D _ hsop

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
