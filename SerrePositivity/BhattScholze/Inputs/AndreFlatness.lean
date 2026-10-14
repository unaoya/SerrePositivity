module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed

/-!
# André の平坦性補題（文献入力）

## 概要

Bhatt–Scholze, *Prisms and prismatic cohomology*, Theorem 7.14（著者版。arXiv v3 では 7.12）を引用する。
任意の perfectoid 環 R に対して、perfectoid 環への p 完全忠実平坦な写像 R → S で、
S が絶対整閉なものが存在する。

## 引用の範囲

原典の主張の第1文だけを引用する。
第2文「特に S の任意の元は両立する p 冪根の系を持つ」は、
`IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots` で証明済みである。
第3文（R → S を mod p で ind-syntomic に取れる、Remark 7.15）は引用しない。
p 完全忠実平坦性は BS §1.2 の定義（`IsCompletelyFaithfullyFlat`）をそのまま使う。
perfectoid 環は `IsIntegralPerfectoid` で、BS が採用する [BMS18, §3] の定義と同じ条件である。

## 証明の状況

原典の証明は Prop 7.11 を経由し、導来 prismatic cohomology と Hodge–Tate 比較を使う。
ここでは証明しない。必要な場合に限った別経路の計画は
`formalization-plans/bhatt-scholze.md` の §5 にある。

## 使われ方

Thm 7.4（semiperfectoid 環の perfectoid 化の全射性）の証明に使う予定である。
2026-10-14 の時点では、まだどの宣言からも使われていない。

出典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf （Theorem 7.14、印刷 p.61）。
-/

@[expose] public section

universe u

namespace SerrePositivity.BhattScholze.Inputs

/-- BS Thm 7.14（André の平坦性補題）：perfectoid 環 R には、perfectoid 環 S への
p 完全忠実平坦な代数構造で、S が絶対整閉となるものが存在する。
S は R と同じ宇宙に取る。原典の構成は R 上の多項式環の商の超限的な余極限なので、宇宙は上がらない。 -/
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S := by
  sorry

end SerrePositivity.BhattScholze.Inputs
