module

public import SerrePositivity.BhattScholze.Andre.Transfinite.FamilyExtension

/-! # BS Thm 7.14：André の完全忠実平坦な絶対整閉拡大

A1 の完全 prism 商上の一元根付き拡大を一般の perfectoid 基底へ移し、
固定した多項式族を一元ずつ飽和させて指定 step を証明する。
その step を ω₁ 反復へ入力する。追加の存在仮定や引用は置かない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
/-- ## 概要
perfectoid 環 R には、perfectoid かつ絶対整閉な環 S への p 完全忠実平坦な代数構造が存在する。
BS Thm 7.14（著者版 p.61）。R と S は同じ Type u に取る。

## 方針
A1 の一元根付き拡大を完全 prism 商表示から一般の perfectoid 基底へ移す。
固定した族を一元ずつ飽和させる後続基数の反復で、正次数条件付きの指定 step を得る。
全正次数モニック多項式の根添加を ω₁ まで反復する既証の存在定理へ、この step を入力する。

## 規約
前提は元の perfectoid 性のみ。一段拡大 step・塔・比較・ねじれ境界を仮定しない。
終段は自動的に p 進完備な環余極限を使い、有限係数の降下と次段の根から絶対整閉性を得る。

## 使われ方
Inputs の元の Thm 7.14 と同じ署名の、追加存在仮定なしの証明を供給する。
原典と異なる一段拡大の PD 経路と一元飽和の補足は計画ファイルに記録する。
-/
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S := by
  apply Transfinite.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  intro B _ hB σ f hf
  exact Transfinite.exists_monicFamilyRootedPerfectoidExtension B p hB f hf
end SerrePositivity.BhattScholze.Andre
