module

public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainFunctoriality

/-!
概要：KST Def3.1・Lemma3.6 の基底変換を dg 関手として構成する。
方針：生成元変換の微分適合性を使い、Hom の可逆性は構成済みの複体同型で示す。
規約：同一重なり環上の外積模型。反復 cone 比較と導来局所化は別工程。
使われ方：導来チャート図式と例外因子の局所比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {B : Type (max u v)} {I : Type v} [CommRing B] [DecidableEq I]

/-- 概要：チャートの可逆 Koszul 基底変換による dg 関手。
方針：線形基底変換の微分適合性を一般の Koszul dg 関手へ渡す。
規約：KST §3.1、x_i=1、s=x_k。使われ方：重なり上の局所 dg 環の比較。 -/
def chartExteriorDGFunctor (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    EnrichedFunctor (DifferentialGraded.Complex B)
      (ExteriorKoszulObject (chartKoszulDifferential a (normalizeCoordinates x s) k))
      (ExteriorKoszulObject (chartKoszulDifferential a x i)) :=
  exteriorKoszulDGFunctor (koszulGeneratorMap i k x s)
    (chartKoszulDifferential a (normalizeCoordinates x s) k)
    (chartKoszulDifferential a x i) (koszulGeneratorMap_differential a x i k s hi hs)

/-- 概要：チャート dg 関手の Hom の射は可逆。
方針：可逆基底変換から構成した cochain 同型を用いる。
規約：KST §3.1、局所化後の共通基底環上。使われ方：チャートの dg 同型への入力。 -/
theorem chartExteriorDGFunctor_map_isIso (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    IsIso ((chartExteriorDGFunctor a x i k s hi hs).map .point .point) := by
  change IsIso (chartExteriorCochainIso a x i k s hi hs).hom
  infer_instance

/-- 概要：例外因子の局所表示から Ko(B;a) の表示への dg 関手。
方針：自己逆な全生成元変換と微分比較を使う。
規約：KST Lemma3.6、B はチャートの多項式環も許す。
使われ方：E∩U_i の外積模型での dg 比較。 -/
def exceptionalExteriorDGFunctor (a x : I → B) (i : I) :
    EnrichedFunctor (DifferentialGraded.Complex B)
      (ExteriorKoszulObject (Finsupp.linearCombination B (exceptionalRelationValue a x i)))
      (ExteriorKoszulObject (Finsupp.linearCombination B a)) :=
  exteriorKoszulDGFunctor (exceptionalGeneratorMap i x)
    (Finsupp.linearCombination B (exceptionalRelationValue a x i))
    (Finsupp.linearCombination B a) (exceptionalGeneratorMap_differential a x i)

/-- 概要：例外因子の比較 dg 関手の Hom の射は可逆。
方針：自己逆基底変換に対応する cochain 同型を使う。
規約：KST Lemma3.6。使われ方：例外因子の局所 dg 比較の可逆性。 -/
theorem exceptionalExteriorDGFunctor_map_isIso (a x : I → B) (i : I) :
    IsIso ((exceptionalExteriorDGFunctor a x i).map .point .point) := by
  change IsIso (exceptionalExteriorCochainIso a x i).hom
  infer_instance

end SerrePositivity.KST.DerivedBlowup
