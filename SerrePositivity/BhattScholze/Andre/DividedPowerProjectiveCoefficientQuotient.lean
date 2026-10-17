module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# André E1・E2：射影的な正次数商を使う任意係数元による分冪降下

## 概要

R 代数 D の分冪イデアル J に対し、D/J が R 上射影的なら、任意の係数元 a による
商へ分冪構造が降りる。BS Rem 7.15(1)（著者版 p.62）のモニック入力の係数還元。

## 方針

D→D/J の R 線形切断を取り、a b∈J を a c（c∈J）と書き直す。
分冪の積公式から係数主イデアルとの交わりの安定性を証明する。
原典とは異なる射影性による切断を使う証明である。

## 規約

係数元の正則性は仮定しない。分冪構造は実際の像イデアルに与える。

## 使われ方

モニック入力による正次数商の自由性から射影性を得て、prism 商の p 正則性を使わずに降下する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} {D : Type v} [CommRing R] [CommRing D] [Algebra R D]
variable {J : Ideal D} [Module.Projective R (D ⧸ J)]

/-- 概要：係数倍が J に入れば同じ係数倍を J 内の元で表せる。
方針：射影的な商への線形切断を b から差し引き、係数倍が変わらないことを示す。
規約：係数元 a の零因子を許す。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数主イデアルと分冪イデアルの交わり。 -/
theorem exists_coefficient_mul_representative_of_projective_quotient
    (a : R) (b : D) (hb : algebraMap R D a * b ∈ J) :
    ∃ c ∈ J, algebraMap R D a * c = algebraMap R D a * b := by
  let q : D →ₗ[R] D ⧸ J := (Ideal.Quotient.mkₐ R J).toLinearMap
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective R J))
  have hs' (y : D ⧸ J) : q (s y) = y := congrArg (fun F : (D ⧸ J) →ₗ[R] D ⧸ J => F y) hs
  let c := b - s (q b)
  have hc : q c = 0 := by
    dsimp only [c]
    rw [map_sub, hs', sub_self]
  have hcJ : c ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hc
  have hqb : a • q b = 0 := by
    rw [← map_smul q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [Algebra.smul_def] using hb)
  have hsb : a • s (q b) = 0 := by
    rw [← map_smul s, hqb, map_zero]
  refine ⟨c, hcJ, ?_⟩
  rw [← Algebra.smul_def, ← Algebra.smul_def]
  change a • (b - s (q b)) = a • b
  rw [smul_sub, hsb, sub_zero]

variable (H : DividedPowers J) (a : R)

/-- 概要：任意の係数主イデアルと分冪イデアルの交わりは分冪で安定。
方針：係数倍を J 内の元の係数倍に書き直し、正次数分冪の積公式を使う。
規約：D/J の R 上の射影性のみを要求し、係数元の正則性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数商への実分冪降下。 -/
theorem dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective :
    H.IsSubDPIdeal (Ideal.span {algebraMap R D a} ⊓ J) := by
  refine ⟨inf_le_right, ?_⟩
  intro n hn x hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx.1
  obtain ⟨c, hcJ, hc⟩ :=
    exists_coefficient_mul_representative_of_projective_quotient a b hx.2
  refine ⟨?_, H.dpow_mem hn hx.2⟩
  rw [← hc, H.dpow_mul hcJ]
  exact Ideal.mem_span_singleton.mpr
    (dvd_mul_of_dvd_left (dvd_pow_self (algebraMap R D a) hn) _)

/-- 概要：射影的な正次数商を持つ実分冪構造は任意係数元の商へ降りる。
方針：係数主イデアルとの交わりの分冪安定性を通常商の構成へ渡す。
規約：元の J の実商射による像イデアルを使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正則性を要求しない係数還元。 -/
def dividedPowersQuotientOfProjectiveCoefficient :
    DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D a}))) :=
  DividedPowers.Quotient.dividedPowers H
    (dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective H a)

/-- 概要：係数還元後の分冪値は還元前の実分冪値の商像。
方針：分冪商の標準評価公式を使う。
規約：全次数 n と元の J の任意の元を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の入力元の分冪値の追跡。 -/
theorem dividedPowersQuotientOfProjectiveCoefficient_apply
    (n : ℕ) {x : D} (hx : x ∈ J) :
    (dividedPowersQuotientOfProjectiveCoefficient H a).dpow n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (H.dpow n x) :=
  DividedPowers.Quotient.dpow_apply H
    (dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective H a) hx

/-- 概要：射影的な正次数商による任意係数還元の商射は分冪射。
方針：構成済みの分冪商の射の互換性を使う。
規約：同じ係数元の主イデアルと同じ像イデアルを比較する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の還元後の pd 普遍性への接続。 -/
theorem dividedPowersQuotientOfProjectiveCoefficient_isDPMorphism :
    H.IsDPMorphism (dividedPowersQuotientOfProjectiveCoefficient H a)
      (Ideal.Quotient.mk (Ideal.span {algebraMap R D a})) :=
  DividedPowers.Quotient.isDPMorphism H
    (dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective H a)

end SerrePositivity.BhattScholze.Andre
