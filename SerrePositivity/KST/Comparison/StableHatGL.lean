module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.HatGLStabilization
public import SerrePositivity.KST.Comparison.GrouplikeColimit
public import SerrePositivity.KST.Comparison.HatGLDelooping
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 安定 rank の ĜL と群完備化の比較

概要：有限 rank の安定化の実際の余極限として安定 ĜL を構成する。
方針：単体的モノイドの図式圏で順序余極限を取り、各段階の群状性を移す。
規約：KST 式 (2.3)、Lemma 2.13 の安定 rank。
使われ方：安定分類空間と高次ホモトピー群の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：単位とのブロック和による有限 rank の ĜL の順序列。
方針：各 rank の単体的モノイドと安定化の自然変換を並べる。
規約：rank 零から始める。
使われ方：安定 rank の余極限の入力。
-/
def hatGLRankSequence (A : SimplicialObject RingCat.{u}) :
    ℕ ⥤ SimplicialObject MonCat.{u} :=
  Functor.ofSequence (hatGLStabilization A)

/--
概要：安定 ĜL は有限 rank の安定化の順序余極限である。
方針：単体的モノイドの図式圏の実際の余極限を取る。
規約：群状モノイドとして扱い、各単体次数で群とは主張しない。
使われ方：KST Lemma 2.13 の安定分類空間。
-/
def stableHatGL (A : SimplicialObject RingCat.{u}) : SimplicialObject MonCat.{u} :=
  colimit (hatGLRankSequence A)

/--
概要：安定 ĜL は群状である。
方針：各有限 rank の群状性を順序余極限へ移す。
規約：成分での可逆性のみを要求する。
使われ方：安定分類空間への Segal 比較。
-/
theorem stableHatGL_isGrouplike (A : SimplicialObject RingCat.{u}) :
    SimplicialMonoid.IsGrouplike (stableHatGL A) :=
  isGrouplike_of_sequential_isColimit (colimit.isColimit (hatGLRankSequence A))
    (hatGL_isGrouplike A)

/--
概要：安定 ĜL の標準群完備化写像は局所化同型である。
方針：実際の安定モノイドの群状性を Segal の標準比較へ適用する。
規約：KST Lemma 2.13 の安定 rank の delooping の比較部分。
使われ方：π_n の具体的な界面への接続。
-/
theorem stableHatGLGroupCompletionMap_localized_isIso (A : SimplicialObject RingCat.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidGroupCompletionMap (stableHatGL A))) :=
  monoidGroupCompletionMap_localized_isIso _ (stableHatGL_isGrouplike A)

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (2.3)" (partial := component) "仮定：単位つき単体環と有限行列の安定化（Lean が強い）。結論：安定 ĜL とその群状性。原典の非単位的単体環を含む安定行列のホモトピー引き戻し正方形全体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.Comparison.stableHatGL
attribute [cite KST "Eq (2.3)" (partial := component) "仮定：単位つき単体環と有限行列の安定化（Lean が強い）。結論：安定 ĜL とその群状性。原典の非単位的単体環を含む安定行列のホモトピー引き戻し正方形全体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.Comparison.stableHatGL_isGrouplike
