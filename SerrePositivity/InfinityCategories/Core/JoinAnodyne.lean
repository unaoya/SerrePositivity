module

public import SerrePositivity.InfinityCategories.Core.JoinLifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：pushout-join の包含の inner anodyne 性。
方針：ホーン・境界セルを相対 slice・coslice の持ち上げ問題を通じて一般の射へ広げる。
規約：左の right anodyne または右の left anodyne が仮定。モデル構造は用いない。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4、slice 射影の右ファイブレーション性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.InfinityCategories

/-- 概要：左因子の包含が right anodyne なら pushout-join の包含は inner anodyne。
方針：右因子を固定した相対 slice の射が右ホーンの rlp を持つことと、生成クラスの llp を使う。
規約：右因子の部分複体包含には追加条件を課さない。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の第一の主張。 -/
@[kerodon 018J]
lemma joinUnion_innerAnodyne_of_rightAnodyne {A B : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (hA : rightAnodyneExtensions A₀.ι) :
    innerAnodyneExtensions (joinUnion A₀ B₀).ι := by
  intro X Y q hq
  apply joinUnion_hasLiftingProperty_of_relativeSliceOverMap
  intro p
  apply hA
  intro C D f hf
  cases hf with
  | @intro n i h0 =>
    exact relativeSliceOverMap_hasLiftingProperty B₀ (horn (n + 1) i) q
      (joinUnion_rightHorn_innerAnodyne B₀ n i h0 q hq) p

/-- 概要：右因子の包含が left anodyne なら pushout-join の包含は inner anodyne。
方針：左因子を固定した相対 coslice の射が左ホーンの rlp を持つことと、生成クラスの llp を使う。
規約：左因子の部分複体包含には追加条件を課さない。
使われ方：HTT Lemma 2.1.2.3、Kerodon Proposition 4.3.6.4 の第二の主張。 -/
@[kerodon 018J]
lemma joinUnion_innerAnodyne_of_leftAnodyne {A B : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (hB : leftAnodyneExtensions B₀.ι) :
    innerAnodyneExtensions (joinUnion A₀ B₀).ι := by
  intro X Y q hq
  apply joinUnion_hasLiftingProperty_of_relativeSliceUnderMap
  intro p
  apply hB
  intro C D f hf
  cases hf with
  | @intro n i hn =>
    exact relativeSliceUnderMap_hasLiftingProperty A₀ (horn (n + 1) i) q
      (joinUnion_leftHorn_innerAnodyne A₀ n i hn q hq) p

end SerrePositivity.InfinityCategories
