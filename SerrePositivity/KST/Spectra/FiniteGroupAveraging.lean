module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.Rat

/-!
概要：有限群の有理表現に対する平均化と不変部分への射影。
方針：群の位数の逆数を norm に掛け、有限和の添字の変更で不変性を示す。
規約：位数が ℚ で非零かつ可逆であることを明示する。
使われ方：BF 1978 §2、HA §1.4.2。L9e の有理群コホモロジー消滅の入力。
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace SerrePositivity.KST.Spectra

noncomputable section

/-- 概要：有限群の位数は有理数体で非零。
方針：群の単位元による非空性と有限性から正の位数を得る。
規約：Nat.card を使い Fintype の選択に依存しない。
使われ方：BF 1978 §2、HA §1.4.2。有理平均化の分母。 -/
theorem finiteGroupOrder_ne_zero (G : Type v) [Group G] [Finite G] :
    (Nat.card G : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.card_pos (α := G)).ne'

/-- 概要：有限群の位数は有理数体で可逆。
方針：非零元は体の単元であることを使う。
規約：平均化で実際に反転する係数。
使われ方：HA §1.4.2。有理 Shapiro の係数条件。 -/
theorem finiteGroupOrder_isUnit (G : Type v) [Group G] [Finite G] :
    IsUnit (Nat.card G : ℚ) := isUnit_iff_ne_zero.mpr (finiteGroupOrder_ne_zero G)

variable {G : Type v} [Group G] [Fintype G]
  {M : Type u} [AddCommGroup M] [Module ℚ M]

/-- 概要：有理表現の平均化作用素。
方針：norm の有限和を群の位数で割る。
規約：表現の元の加法構造を用いる。
使われ方：BF 1978 §2、HA §1.4.2。有理不変部分への実際の線形射影。 -/
def rationalAverage (ρ : Representation ℚ G M) : Module.End ℚ M :=
  (Nat.card G : ℚ)⁻¹ • ρ.norm

/-- 概要：平均化の像は群の全ての元で固定される。
方針：norm の左不変性と表現の線形性を使う。
規約：任意の有理表現。
使われ方：BF 1978 §2、HA §1.4.2。不変部分への射影の像の計算。 -/
theorem rationalAverage_invariant (ρ : Representation ℚ G M) (g : G) (x : M) :
    ρ g (rationalAverage ρ x) = rationalAverage ρ x := by
  simp only [rationalAverage, LinearMap.smul_apply, map_smul, Representation.self_norm_apply]

/-- 概要：平均化は不変な元を保つ。
方針：有限和を定数和にし、群の位数とその逆を打ち消す。
規約：分母の非零性は有限群の単位元から得る。
使われ方：BF 1978 §2、HA §1.4.2。平均化が不変部分上の恒等射であること。 -/
theorem rationalAverage_eq_of_invariant (ρ : Representation ℚ G M) (x : M)
    (hx : ∀ g, ρ g x = x) : rationalAverage ρ x = x := by
  have hs : ρ.norm x = (Fintype.card G : ℚ) • x := by
    simp only [Representation.norm, LinearMap.sum_apply, hx, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [rationalAverage, LinearMap.smul_apply, hs, Fintype.card_eq_nat_card,
    smul_smul, inv_mul_cancel₀ (finiteGroupOrder_ne_zero G), one_smul]

/-- 概要：有理平均化は冪等。
方針：像の不変性に不変元での恒等性を適用する。
規約：加法群の準同型としても射影である。
使われ方：BF 1978 §2、HA §1.4.2。有理群コホモロジーの消滅と次数零の同定。 -/
theorem rationalAverage_idempotent (ρ : Representation ℚ G M) (x : M) :
    rationalAverage ρ (rationalAverage ρ x) = rationalAverage ρ x :=
  rationalAverage_eq_of_invariant ρ _ (fun g ↦ rationalAverage_invariant ρ g x)

end

end SerrePositivity.KST.Spectra
