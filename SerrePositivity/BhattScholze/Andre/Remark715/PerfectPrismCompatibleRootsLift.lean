module

public import SerrePositivity.BhattScholze.Andre.Remark715.CommonAdicCompatibleRoots
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismPairAdicComplete

/-!
# André E1・E2：完全試験 prism の剰余互換根列の一意持上げ

## 概要

完全 prism の商にある互換 p 冪根列は、台環内の互換根列へ一意に持ち上がる。
BS Rem 7.15（著者版 p.62）の絶対 prismatic 入力射の完全試験環での持上げ。

## 方針

台環の (p,d) 完備性と商の p 完備性を、共通完備商による Perfection の同型へ供給する。
原典とは異なる Teichmüller モノイド比較による経路。

## 規約

試験 prism の完全性を明示する。商の p 正則性・非零性は仮定しない。
一般の試験 prism に対する同じ完備性の供給は別工程。

## 使われ方

剰余根列を入力として、完全試験 prism への実完備化の普遍射を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : OrientedPrism p B)

/-- 概要：共通二元イデアルの prism 商での像は p 主イデアル。
方針：商で生成元 d が零になることを二元生成イデアルの像へ代入する。
規約：この計算自体に完全性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の二つの古典的完備性の比較。 -/
theorem prism_pair_map_ideal_eq_prime :
    (Ideal.span {(p : B), Q.generator}).map (Ideal.Quotient.mk Q.ideal) =
      Ideal.span {(p : B ⧸ Q.ideal)} := by
  rw [Ideal.map_span, Set.image_pair, map_natCast]
  have hd : Ideal.Quotient.mk Q.ideal Q.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self Q.generator)
  rw [hd, Ideal.span_pair_zero]

/-- 概要：完全 prism 商の互換根列は台環内へ一意に持ち上がる。
方針：(p,d) 完備性と商の p 完備性を共通完備商の根列持上げへ適用する。
規約：零環を含み、商の p 正則性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の完全試験 prism 内への根列の持上げ。 -/
theorem existsUnique_perfectPrismCompatibleRootsLift
    (hQ : Q.deltaStructure.IsPerfect) (ρ : ℕ → B ⧸ Q.ideal)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! σ : ℕ → B,
      (∀ n, σ (n + 1) ^ p = σ n) ∧ ∀ n, Ideal.Quotient.mk Q.ideal (σ n) = ρ n := by
  let I := Ideal.span {(p : B), Q.generator}
  let := Q.isAdicComplete_p_of_perfect hQ
  let : IsAdicComplete I B := perfectPrism_pair_isAdicComplete Q hQ
  let : IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
    hQ.distinguished_quotient_isAdicComplete (Q.isDistinguished_of_perfect hQ)
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
