module
public import SerrePositivity.KST.SConstruction.SOneComparison
public import SerrePositivity.KST.SConstruction.TrivialFibrationUniversality

/-! # S₁ の比較の完全性と安定圏での自然性
概要：S₁ の比較は零対象と全押し出しを保ち、安定圏の自然変換を与える。
方針：既存の trivial Kan fibration による普遍性の保存を適用する。
規約：逆射や補完を自然に選択しない。使われ方：反復 S の一次方向の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：S₁ の比較は零対象と全押し出しを保存する。
方針：trivial Kan fibration の普遍性の保存を適用する。
規約：C は安定な quasicategory。使われ方：安定圏の射への束ね直し。 -/
lemma sOneComparison_preservesSConstructionData (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    PreservesSConstructionData (sOneComparison C) :=
  preservesSConstructionData_of_trivialKanFibration _

/-- 概要：S₁ の比較は cofiber 保存条件を満たす。
方針：全押し出しの保存を零角付き正方形に制限する。
規約：追加の保存仮定は不要。使われ方：反復 S の入力の射。 -/
lemma sOneComparison_preservesCofiberData (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    PreservesCofiberData (sOneComparison C) :=
  (sOneComparison_preservesSConstructionData C).toCofiberData

/-- 概要：S₁ の比較を安定圏の射としてまとめる。
方針：cofiber 保存条件を添える。
規約：底の射は既存の比較と同じ。使われ方：反復中の自然な比較。 -/
def stableSOneComparison (X : StableModel.{u}) : (sEndofunctor 1).obj X ⟶ X :=
  ⟨sOneComparison X.carrier, sOneComparison_preservesCofiberData X.carrier⟩

/-- 概要：S₁ の比較は安定圏上の自然変換。
方針：既存の底の単体集合での自然性を部分型へ持ち上げる。
規約：零対象の厳密な選択保存を要求しない。使われ方：多単体的反復の比較。 -/
def stableSOneComparisonNat : sEndofunctor 1 ⟶ 𝟭 StableModel.{u} where
  app := stableSOneComparison
  naturality {_X _Y} f := Subtype.ext (sOneComparison_naturality f.val f.property)

end SerrePositivity.KST.SConstruction
