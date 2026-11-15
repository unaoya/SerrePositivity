module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import SerrePositivity.BhattScholze.Andre.Transfinite.Tower

/-!
# André の平坦性補題の証明済み公開入口

## 概要

Bhatt–Scholze, *Prisms and prismatic cohomology*, BS 著者版 Theorem 7.14（著者版 p.61）の第一文を証明する。
perfectoid 環 R には、同じ宇宙の perfectoid・絶対整閉な環 S への
p 完全忠実平坦な代数構造が存在する。

## 方針

`Andre/Transfinite/Tower.lean` の追加仮定のない存在定理を使う。
A1 の完全 prism 商上の一元拡大を一般の perfectoid 基底へ移し、固定した族の一元飽和により
任意族の一段根付き拡大を証明する。それを ω₁ まで反復し、自動的に p 進完備な終段で
有限係数の降下と後続段の根から絶対整閉性を得る。
原典の BS 著者版 Proposition 7.11（導来 prismatic コホモロジー）を経由する証明とは異なり、一元拡大はモニック根の
割り算包（PD 経路）で構成する。任意の族は後続基数による一元ずつの飽和で扱い、ω₁ 反復は
`SmallObject.SuccStruct.iterationFunctor` で実装する。数学の説明は解説の `par:bs-andre`。

## 規約

公開署名と p 完全忠実平坦性の定義を保持する。一段拡大 step や塔を仮定しない。
第二文の両立する p 冪根は `IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots` で証明済み。
BS 著者版 Remark 7.15（p.62）の mod p で ind-syntomic に取れるという強化は、この公開定理の結論に含めない。

## 使われ方

両立する根の選択と perfectoid 化の全射性などに、
元の Inputs の署名のまま、証明済みの André 拡大を供給する。
-/

@[expose] public section

universe u

namespace SerrePositivity.BhattScholze.Inputs

/-- ## 概要
perfectoid 環 R には、同じ Type u の perfectoid・絶対整閉環 S への
p 完全忠実平坦な代数構造が存在する（BS 著者版 Theorem 7.14 の第一文）。

## 方針
一元根添加から任意族の step を証明し、ω₁ 反復を構成した既証の存在定理を適用する。

## 規約
元の公開署名を保持する。前提は R の perfectoid 性のみ。

## 使われ方
André 拡大を使う既存の公開入口として、追加仮定のない存在証明を返す。
-/
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S := by
  exact
    SerrePositivity.BhattScholze.Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
      R p hR

end SerrePositivity.BhattScholze.Inputs

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 7.14"] _root_.SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
