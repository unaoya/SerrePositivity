module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialDeltaUniversal
public import SerrePositivity.BhattScholze.Andre.Remark715.BoundedPrismCompatibleRootsLift

/-!
# André E1・E2：有界試験 prism の剰余根列からの無限根入力 δ 射

## 概要

有界試験 prism の剰余内にある互換根列と基底 δ 射から、
剰余根列を保つ無限根入力 δ 射が一意に存在する。
BS Rem 7.15（著者版 p.62）の入力 δ 射の持上げの有界試験環での計算。

## 方針

共通完備商による根列の一意持上げを行い、p 進分離性で rank 1 性を供給する。
原典とは異なる Perfection モノイド同型・有理指数の評価・W₂ 切断による経路。

## 規約

試験 prism の完全性は要求せず、有界性を明示する。源の δ 環には p 正則性のみを要求する。
試験 prism の商の p 正則性や非零性を仮定しない。

## 使われ方

指定入力 δ 射を前提とせず、原典の剰余上の根データから実完備化への射を作る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
variable {B : Type v} [CommRing B]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：完全 prism の剰余互換根列を保つ無限根入力 δ 射は一意に存在。
方針：実根列への一意持上げと rank 1 根列の δ 普遍性を合成する。
規約：根列は商内に与え、台環内の根列や δ 条件を引数に残さない。
使われ方：BS Rem 7.15（著者版 p.62）の有界試験 prism に対する入力射の一意持上げ。 -/
theorem existsUnique_powerRootPolynomialDeltaHom_of_boundedPrism_residue_roots
    (hpR : Function.Injective (fun x : R => (p : R) * x)) (D : DeltaStructure p R)
    (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : R →+* B) (hk : D.IsDeltaHom Q.deltaStructure k)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! g : P →+* B,
      (powerRootPolynomialDelta p hpR D).IsDeltaHom Q.deltaStructure g ∧
        g.comp (algebraMap R P) = k ∧
          ∀ n, Ideal.Quotient.mk Q.ideal (g (powerRootPolynomialVariable R p hp n)) = ρ n := by
  let := boundedPrism_isHausdorff_prime Q hB
  obtain ⟨σ, hσ, hσu⟩ := existsUnique_boundedPrismCompatibleRootsLift Q hB ρ hρ
  obtain ⟨g, hg, hu⟩ := existsUnique_powerRootPolynomialDeltaHom_of_isHausdorff p hpR D
    Q.deltaStructure k hk σ hσ.1
  refine ⟨g, ⟨hg.1, hg.2.1, ?_⟩, ?_⟩
  · intro n
    exact (congrArg (Ideal.Quotient.mk Q.ideal) (hg.2.2 n)).trans (hσ.2 n)
  · intro K hK
    let τ := fun n => K (powerRootPolynomialVariable R p hp n)
    have hτ : ∀ n, τ (n + 1) ^ p = τ n := by
      intro n
      exact (map_pow K _ p).symm.trans
        (congrArg K (powerRootPolynomialVariable_pow R p hp n))
    have hτσ : τ = σ := hσu τ ⟨hτ, hK.2.2⟩
    apply hu K
    exact ⟨hK.1, hK.2.1, fun n => congrFun hτσ n⟩

end SerrePositivity.BhattScholze.Andre
