module

public import SerrePositivity.BhattScholze.Andre.BoundedPrismAdicComplete

/-!
# André A1-a：有界 prism の台環の古典的 p 完備性

## 概要

導来主元完備で主元進分離な環は古典的に完備である。これを有界 prism に適用する。
BS Lemma 4.8（著者版 pp.38–39）の基底射の存在と Rem 7.15（p.62）の入力比較の準備。

## 方針

導来完備性から列の差分作用の全射性を得て前完備性を供給し、既知の分離性と合わせる。
有界 prism では (p,d) 分離性から得た p 分離性を使う。原典とは異なる直接比較の経路。

## 規約

p の正則性や台環の有界 p ねじれは仮定しない。基底射の存在自体はまだ主張しない。

## 使われ方

一般有界 prism への Witt 環からの持上げで、台環の古典的 p 完備性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：導来主元完備かつ主元進分離な環は古典的に主元進完備。
方針：差分作用の全射性から前完備性を得て、分離性と合わせる。
規約：主元の正則性は要求しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の一般有界標的への持上げの準備。 -/
theorem isAdicComplete_of_isModuleComplete_of_isHausdorff
    (R : Type u) [CommRing R] (a : R)
    (h : DerivedCompletion.IsModuleComplete R a (ModuleCat.of R R))
    [IsHausdorff (Ideal.span {a}) R] : IsAdicComplete (Ideal.span {a}) R := by
  have hb := (DerivedCompletion.isModuleComplete_iff_recurrence_bijective
    R a (ModuleCat.of R R)).mp h
  let := isPrecomplete_of_adicRecurrenceMap_surjective a hb.2
  exact ⟨⟩

/-- 概要：有界 prism の台環は古典的に p 完備である。
方針：導来 p 完備性と (p,d) 分離性からの p 分離性を一般比較へ渡す。
規約：標的の完全性・p 正則性・台環の有界 p ねじれは要求しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）と Rem 7.15（p.62）の入力射の構成。 -/
theorem boundedPrism_isAdicComplete_prime
    {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0) :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  let := boundedPrism_isHausdorff_prime Q hB
  exact isAdicComplete_of_isModuleComplete_of_isHausdorff B (p : B) Q.complete_p

end SerrePositivity.BhattScholze.Andre
