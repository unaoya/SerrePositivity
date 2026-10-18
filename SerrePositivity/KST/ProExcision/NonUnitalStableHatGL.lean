module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGLGrouplike
public import SerrePositivity.KST.ProExcision.NonUnitalHatGLBlock
public import SerrePositivity.KST.Comparison.GrouplikeColimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 非単位単体環の安定一般線形モノイド

概要：非単位環の ĜL を有限 rank の実順序余極限として構成する。
方針：単位ブロック和による各 rank の実単体射を順序列にし、群状性を実余極限へ移す。
規約：KST Proposition 4.14・Claim 4.15、各次数の群性は要求しない。
使われ方：有限 rank の相対零化から安定 rank の相対零化への移行。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits

/-- 概要：非単位環の有限 rank の ĜL の順序列。
方針：新しい単位座標を末尾に一つずつ加える。
規約：KST Claim 4.15、rank 零も含む。使われ方：安定一般線形モノイドの実定義。 -/
def NonUnitalSimplicialRing.hatGLRankSequence (I : NonUnitalSimplicialRing.{u}) :
    ℕ ⥤ SimplicialObject MonCat.{u} :=
  Functor.ofSequence (fun n ↦ I.hatGLBlockMap n 1)

/-- 概要：非単位単体環の安定 ĜL を実順序余極限として定義する。
方針：単体的モノイドの圏で rank の列の余極限を取る。
規約：KST Proposition 4.14、π₀ でのみ可逆性を要求する。
使われ方：安定 bar と相対ホモロジーの値域。 -/
def NonUnitalSimplicialRing.stableHatGL (I : NonUnitalSimplicialRing.{u}) :
    SimplicialObject MonCat.{u} := colimit I.hatGLRankSequence

/-- 概要：非単位環の安定 ĜL は実際に群状。
方針：各有限 rank の証明済みの群状性を実順序余極限へ移す。
規約：KST Proposition 4.14、次数ごとの逆元は追加しない。
使われ方：安定半直積の相対比較と群完備化の界面。 -/
lemma NonUnitalSimplicialRing.stableHatGL_isGrouplike (I : NonUnitalSimplicialRing.{u}) :
    Comparison.SimplicialMonoid.IsGrouplike I.stableHatGL :=
  Comparison.isGrouplike_of_sequential_isColimit (colimit.isColimit I.hatGLRankSequence)
    I.hatGL_isGrouplike

/-- 概要：各有限 rank から安定 ĜL への実単体射。
方針：実余極限の標準脚を用いる。
規約：KST Proposition 4.14。使われ方：有限 rank の代表の安定化。 -/
def NonUnitalSimplicialRing.stableHatGLInclusion (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    I.hatGL n ⟶ I.stableHatGL := colimit.ι I.hatGLRankSequence n

end SerrePositivity.KST.ProExcision
