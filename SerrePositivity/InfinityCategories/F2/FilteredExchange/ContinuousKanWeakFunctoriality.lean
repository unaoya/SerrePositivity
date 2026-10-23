module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanWeakEquivalence

/-!
概要：具体的な連続 Kan 置換は任意の単体集合間の弱同値を保つ。
方針：単位の自然性と、その両成分の弱同値性に二対三則を適用する。
規約：元の二対象に Kan 性を仮定しない。
使われ方：Over 圏の augmentation を Kan 値図式の比較に移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：連続 Kan 置換による射の像は元の弱同値性を保つ。
方針：二つの単位と自然性の正方形に弱同値の左消去を使う。
規約：元の射の始域・終域の充填性は不要。使われ方：図式の点ごとの置換。 -/
lemma continuousKanReplacement_map_isWeakHomotopyEquivalence {X Y : SSet.{u}}
    (f : X ⟶ Y) (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (continuousKanReplacement.map f) := by
  apply (continuousKanReplacementUnit_isWeakHomotopyEquivalence X).cancel_left
  have hn : continuousKanReplacementUnit.app X ≫ continuousKanReplacement.map f =
      f ≫ continuousKanReplacementUnit.app Y := (continuousKanReplacementUnit.naturality f).symm
  rw [hn]
  exact hf.comp (continuousKanReplacementUnit_isWeakHomotopyEquivalence Y)

end SerrePositivity.InfinityCategories.F2
