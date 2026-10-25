module

public import SerrePositivity.BhattScholze.Andre.Remark715.BoundedPrismAdicComplete
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismCompatibleRootsLift

/-!
# André E1・E2：一般有界試験 prism の剰余互換根列の一意持上げ

## 概要

有界 prism の商内の互換 p 冪根列は、台環内の互換根列へ一意に持ち上がる。
BS Rem 7.15（著者版 p.62）の prismatic 入力射の持上げに使う。

## 方針

生成元の全冪商の有界ねじれから (p,d) 完備性を供給し、共通完備商の Perfection 同型を使う。
原典とは異なる有界指数の帰納計算と Teichmüller モノイド比較による経路。

## 規約

試験 prism の完全性・p 正則性・商の非零性は不要。有界 p 冪ねじれのみを明示する。

## 使われ方

一般有界試験 prism の剰余根データから実入力 δ 射を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : OrientedPrism p B)

/-- 概要：有界 prism 商の互換根列は台環内へ一意に持ち上がる。
方針：台環の (p,d) 完備性と商の p 完備性を共通完備商の一般結果へ渡す。
規約：完全性や p 正則性を要求せず、零環も含む。
使われ方：BS Rem 7.15（著者版 p.62）の一般有界試験 prism への根列の持上げ。 -/
theorem existsUnique_boundedPrismCompatibleRootsLift
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! σ : ℕ → B,
      (∀ n, σ (n + 1) ^ p = σ n) ∧ ∀ n, Ideal.Quotient.mk Q.ideal (σ n) = ρ n := by
  let I := Ideal.span {(p : B), Q.generator}
  let : IsAdicComplete I B := boundedPrism_pair_isAdicComplete Q hB
  let : IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
    boundedPrism_quotient_isAdicComplete_prime Q hB
  let : IsAdicComplete (I.map (Ideal.Quotient.mk Q.ideal)) (B ⧸ Q.ideal) := by
    rw [prism_pair_map_ideal_eq_prime]
    infer_instance
  have hJI : Q.ideal ≤ I := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.subset_span (by simp)
  exact existsUnique_compatiblePowerRootsLift_of_adic_ideals p I Q.ideal hJI
    (Ideal.subset_span (by simp)) ρ hρ

end SerrePositivity.BhattScholze.Andre
