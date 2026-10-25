module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialUniversal
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialDelta
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta

/-!
# André E1・E2：rank 1 の互換根列による無限根 δ 射の普遍性

## 概要

互換根列の全ての δ が零なら、係数 δ 射と根列から一意な無限根 δ 射が得られる。
BS Rem 7.15（著者版 p.62）の指定入力 δ 射を根データで構成する。

## 方針

二つの W₂ 切断の合成を係数・全根変数上で比較し、通常環射の外延性を使う。
原典の記述を補う有理指数の普遍射と Witt 座標による経路。

## 規約

係数環には無限根 δ 構造を定義する p 正則性を要求する。
終域の p 正則性・完備性・完全性は仮定しない。

## 使われ方

絶対 prismatic envelope との比較に向け、指定 δ 射を係数と根のデータから作る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
variable {B : Type v} [CommRing B]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：無限根環からの環射が係数・全根変数上で δ と可換なら δ 射。
方針：二つの W₂ 切断の合成を通常環射の外延性と二つの Witt 座標で比較する。
規約：源の δ 構造は任意で、終域には p ねじれを許す。
使われ方：BS Rem 7.15（著者版 p.62）の無限根入力射の δ 条件。 -/
theorem isDeltaHom_powerRootPolynomial
    (D : DeltaStructure p P) (E : DeltaStructure p B) (g : P →+* B)
    (hcoeff : ∀ a : R, g (D.delta (algebraMap R P a)) = E.delta (g (algebraMap R P a)))
    (hroot : ∀ n, g (D.delta (powerRootPolynomialVariable R p hp n)) =
      E.delta (g (powerRootPolynomialVariable R p hp n))) : D.IsDeltaHom E g := by
  apply (D.isDeltaHom_iff_sectionHom_comp E g).mpr
  apply powerRootPolynomial_ringHom_ext p hp
  · apply RingHom.ext
    intro a
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact congrArg g (D.coeff_zero (algebraMap R P a)) |>.trans
        (E.coeff_zero (g (algebraMap R P a))).symm
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact hcoeff a
  · intro n
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact congrArg g (D.coeff_zero (powerRootPolynomialVariable R p hp n)) |>.trans
        (E.coeff_zero (g (powerRootPolynomialVariable R p hp n))).symm
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact hroot n

/-- 概要：p 進分離な δ 環の互換根列は全て rank 1 である。
方針：後続の根を各 p 冪根の証人にし、既存の分離性による δ=0 判定を使う。
規約：終域の p 正則性や根列の非零性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の根データに課す δ 条件を自動で供給する。 -/
theorem compatiblePowerRoots_delta_eq_zero (E : DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B]
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) : E.delta (ρ n) = 0 :=
  E.delta_eq_zero_of_has_pow_roots (ρ n) (fun m =>
    ⟨ρ (n + m), compatiblePowerRoots_iterate p ρ hρ n m⟩)

variable (hpR : Function.Injective (fun a : R => (p : R) * a))
variable (D : DeltaStructure p R) (E : DeltaStructure p B) (f : R →+* B)
variable (hf : D.IsDeltaHom E f) (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
variable (hδρ : ∀ n, E.delta (ρ n) = 0)

include hf hδρ in
/-- 概要：係数 δ 射と rank 1 の互換根列による評価射は δ 射。
方針：標準無限根 δ 構造の係数公式と根変数の δ=0 を一般の判定へ渡す。
規約：終域の p ねじれや完備性には制約しない。
使われ方：BS Rem 7.15（著者版 p.62）の根データからの実入力 δ 射。 -/
theorem powerRootPolynomialEval_isDeltaHom :
    (powerRootPolynomialDelta p hpR D).IsDeltaHom E (powerRootPolynomialEval p hp f ρ hρ) := by
  apply isDeltaHom_powerRootPolynomial p
  · intro a
    rw [← powerRootPolynomialDelta_coeff_isDeltaHom p hpR D a,
      powerRootPolynomialEval_coeff, powerRootPolynomialEval_coeff, hf a]
  · intro n
    rw [powerRootPolynomialDelta_variable, map_zero, powerRootPolynomialEval_variable, hδρ]

include hf hρ hδρ in
/-- 概要：係数と rank 1 の互換根列を保つ δ 射は一意に存在。
方針：具体的評価射の δ 性を存在側に使い、通常環射の外延性で一意性を得る。
規約：根の δ=0 と隣接根関係を明示し、prism の完備性や終域の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の指定入力射を根データへ置き換える。 -/
theorem existsUnique_powerRootPolynomialDeltaHom :
    ∃! g : P →+* B,
      (powerRootPolynomialDelta p hpR D).IsDeltaHom E g ∧
        g.comp (algebraMap R P) = f ∧
          ∀ n, g (powerRootPolynomialVariable R p hp n) = ρ n := by
  obtain ⟨g, hg, hu⟩ := existsUnique_powerRootPolynomialHom p hp f ρ hρ
  have hgeval : g = powerRootPolynomialEval p hp f ρ hρ := by
    apply powerRootPolynomial_ringHom_ext p hp g _
    · apply RingHom.ext
      intro a
      exact (RingHom.congr_fun hg.1 a).trans (powerRootPolynomialEval_coeff p hp f ρ hρ a).symm
    · intro n
      exact (hg.2 n).trans (powerRootPolynomialEval_variable p hp f ρ hρ n).symm
  refine ⟨g, ⟨?_, hg⟩, ?_⟩
  · rw [hgeval]
    exact powerRootPolynomialEval_isDeltaHom p hpR D E f hf ρ hρ hδρ
  · intro k hk
    exact hu k hk.2

include hf hρ in
/-- 概要：p 進分離な終域の互換根列へ、係数と根を保つ δ 射が一意に存在する。
方針：全根の rank 1 性を分離性から導き、一般の根データの δ 普遍性を使う。
規約：終域の p 正則性を要求せず、δ=0 を追加引数に残さない。
使われ方：BS Rem 7.15（著者版 p.62）の分離な試験環への入力 δ 射。 -/
theorem existsUnique_powerRootPolynomialDeltaHom_of_isHausdorff
    [IsHausdorff (Ideal.span {(p : B)}) B] :
    ∃! g : P →+* B,
      (powerRootPolynomialDelta p hpR D).IsDeltaHom E g ∧
        g.comp (algebraMap R P) = f ∧
          ∀ n, g (powerRootPolynomialVariable R p hp n) = ρ n :=
  existsUnique_powerRootPolynomialDeltaHom p hpR D E f hf ρ hρ
    (compatiblePowerRoots_delta_eq_zero p E ρ hρ)

end SerrePositivity.BhattScholze.Andre
