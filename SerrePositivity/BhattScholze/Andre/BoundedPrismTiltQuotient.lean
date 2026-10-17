module

public import SerrePositivity.BhattScholze.Andre.BoundedPrismPrimeComplete
public import SerrePositivity.BhattScholze.Andre.BoundedPrismCompatibleRootsLift
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality

/-!
# André A1-a：有界 prism の台環と商の tilt 比較

## 概要

有界 prism の台環から prism 商への射は tilt の環同型を誘導する。
BS Lemma 4.8（著者版 pp.38–39）の基底環射の構成への準備。

## 方針

二つの p 完備環の tilt を実互換根列と乗法的に比較する。
既知の prism 商からの根列の一意持上げにより標準 tilt 環射の全単射性を示す。
原典の変形理論とは異なる Teichmüller 比較の経路。

## 規約

標的 prism の完全性・p 正則性は要求しない。台環と prism 商で p が非可逆である場合を扱う。
台環での非可逆性は商での非可逆性から従うが、型クラス用に明示する。

## 使われ方

商の tilt へ写された完全係数を台環の tilt へ戻し、Fontaine 写像による環射構成に用いる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : OrientedPrism p B)
variable [Fact (¬ IsUnit (p : B))]
variable [Fact (¬ IsUnit (p : B ⧸ Q.ideal))]

variable (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)

include hB in
/-- 概要：有界 prism の商射が誘導する標準 tilt 環射は全単射。
方針：二つの p 完備性から実根列と比較し、既存の根列の一意持上げを使う。
規約：台環と商での p 非可逆性を標数インスタンス用に明示する。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の基底環射を tilt から構成する。 -/
theorem boundedPrism_preTiltQuotient_bijective :
    Function.Bijective (Perfection.map p (modPMap p (Ideal.Quotient.mk Q.ideal))) := by
  let q := Ideal.Quotient.mk Q.ideal
  let := boundedPrism_isAdicComplete_prime Q hB
  let := boundedPrism_quotient_isAdicComplete_prime Q hB
  let eB := Perfection.quotientMulEquiv p (Ideal.span {(p : B)})
  let eC := Perfection.quotientMulEquiv p (Ideal.span {(p : B ⧸ Q.ideal)})
  let M := Perfection.mapMonoidHom p q.toMonoidHom
  have hM : Function.Bijective M := by
    have hex (y : Perfection (B ⧸ Q.ideal) p) : ∃! x : Perfection B p, M x = y := by
      obtain ⟨σ, hσ, hu⟩ := existsUnique_boundedPrismCompatibleRootsLift Q hB
        (fun n => Perfection.coeffMonoidHom (B ⧸ Q.ideal) p n y)
        (fun n => Perfection.coeffMonoidHom_pow_p' y n)
      let x : Perfection B p := ⟨σ, hσ.1⟩
      refine ⟨x, ?_, ?_⟩
      · exact Perfection.extMonoid hσ.2
      · intro z hz
        have hc : (fun n => Perfection.coeffMonoidHom B p n z) = σ := by
          apply hu
          constructor
          · exact fun n => Perfection.coeffMonoidHom_pow_p' z n
          · intro n
            exact congrArg (Perfection.coeffMonoidHom (B ⧸ Q.ideal) p n) hz
        exact Perfection.extMonoid (congrFun hc)
    constructor
    · intro x y hxy
      obtain ⟨z, hz, hu⟩ := hex (M x)
      exact (hu x rfl).trans (hu y hxy.symm).symm
    · intro y
      obtain ⟨x, hx, _⟩ := hex y
      exact ⟨x, hx⟩
  have hcomm (x : Perfection B p) :
      Perfection.map p (modPMap p q) (eB x) = eC (M x) := by
    apply Perfection.ext
    intro n
    rfl
  constructor
  · intro x y hxy
    have he : M (eB.symm x) = M (eB.symm y) := by
      apply eC.injective
      rw [← hcomm, ← hcomm, eB.apply_symm_apply, eB.apply_symm_apply, hxy]
    have h := congrArg eB (hM.injective he)
    simpa only [eB.apply_symm_apply] using h
  · intro y
    obtain ⟨x, hx⟩ := hM.surjective (eC.symm y)
    refine ⟨eB x, ?_⟩
    rw [hcomm, hx, eC.apply_symm_apply]

/-- 概要：有界 prism の台環と prism 商の tilt は標準商射により環同型。
方針：標準 tilt 環射の全単射性から環同型を作る。
規約：完全性や p 正則性を追加せず、有界性と台環・商での p 非可逆性を明示する。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の完全係数の台環への持上げ。 -/
def boundedPrism_preTiltQuotientEquiv : PreTilt B p ≃+* PreTilt (B ⧸ Q.ideal) p := by
  exact RingEquiv.ofBijective
    (Perfection.map p (modPMap p (Ideal.Quotient.mk Q.ideal)))
    (boundedPrism_preTiltQuotient_bijective Q hB)

/-- 概要：tilt 比較同型の各座標は標準 mod p 商射で与えられる。
方針：全単射から作った環同型の順射の定義を展開する。
規約：全ての根段 n で同じ標準商射を使う。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の Fontaine 写像との可換図式。 -/
theorem boundedPrism_preTiltQuotientEquiv_coeff (x : PreTilt B p) (n : ℕ) :
    PreTilt.coeff n (boundedPrism_preTiltQuotientEquiv Q hB x) =
      modPMap p (Ideal.Quotient.mk Q.ideal) (PreTilt.coeff n x) := rfl

end SerrePositivity.BhattScholze.Andre
