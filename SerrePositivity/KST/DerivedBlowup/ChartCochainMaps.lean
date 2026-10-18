module

public import SerrePositivity.KST.DerivedBlowup.ExteriorComplexIso
public import SerrePositivity.KST.DerivedBlowup.ExceptionalBasis

/-!
概要：KST Def3.1・Lemma3.6 のチャートと例外因子の基底変換を整数次数の複体同型にする。
方針：構成済みの可逆生成元変換と微分適合性を exteriorKoszulCochainIso に渡す。
規約：同一重なり環上の外積模型。既存の反復 cone 模型との比較はまだ含まない。
使われ方：導来チャートの複体の貼り合わせと E∩U_i の Ko(A;a)[S] への比較。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {B : Type u} [CommRing B] {I : Type v} [DecidableEq I]

/-- 概要：規格化座標でのチャートの整数次数の外積 Koszul 複体。
方針：生成元の微分 a_i x_j−a_j を外積複体にする。
規約：KST Def3.1、x_i=1 は比較時に要求。使われ方：チャート遷移の定義域と値域。 -/
abbrev chartExteriorCochain (a x : I → B) (i : I) :=
  exteriorKoszulCochain (chartKoszulDifferential a x i)

/-- 概要：チャートの重なりでの整数次数の Koszul 複体の同型。
方針：可逆生成元変換と関係式の微分比較を使う。
規約：KST §3.1、x_i=1、s=x_k。使われ方：dg チャートの underlying 複体の貼り合わせ。 -/
def chartExteriorCochainIso (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    chartExteriorCochain a (normalizeCoordinates x s) k ≅ chartExteriorCochain a x i :=
  exteriorKoszulCochainIso (koszulGeneratorEquiv i k x s hi hs)
    (chartKoszulDifferential a (normalizeCoordinates x s) k) (chartKoszulDifferential a x i)
    (koszulGeneratorMap_differential a x i k s hi hs)

/-- 概要：例外因子の全関係式による整数次数の Koszul 複体。
方針：pivot の Cartier 方程式と残りのチャート方程式を全添字に配置する。
規約：KST Lemma3.6。使われ方：Ko(A;a)[S] との外積模型での比較。 -/
abbrev exceptionalExteriorCochain (a x : I → B) (i : I) :=
  exteriorKoszulCochain (Finsupp.linearCombination B (exceptionalRelationValue a x i))

/-- 概要：例外因子の表示を全 a_j の Koszul 複体へ同定する整数次数同型。
方針：自己逆な基底変換と微分比較を外積複体へ持ち上げる。
規約：KST Lemma3.6、反復 cone との比較とは分離。
使われ方：E∩U_i ≃ Ko(A;a)[S] の複体部分。 -/
def exceptionalExteriorCochainIso (a x : I → B) (i : I) :
    exceptionalExteriorCochain a x i ≅
      exteriorKoszulCochain (Finsupp.linearCombination B a) :=
  exteriorKoszulCochainIso (exceptionalGeneratorEquiv i x)
    (Finsupp.linearCombination B (exceptionalRelationValue a x i)) (Finsupp.linearCombination B a)
    (exceptionalGeneratorMap_differential a x i)

end SerrePositivity.KST.DerivedBlowup
