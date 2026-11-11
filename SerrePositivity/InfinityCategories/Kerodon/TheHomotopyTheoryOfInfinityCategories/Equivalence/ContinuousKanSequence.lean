module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HornCellContinuity
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：連続なホーンセル付加の可算反復とその余極限関手。
方針：恒等関手から始め、一段の付加を反復し、関手圏で余極限を取る。
規約：Kan 性と単位の弱同値性は別に証明する。連続性を構造の仮定にしない。
使われ方：有限境界の因子分解を保つ具体的な Kan 置換。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：ホーンセル付加を n 回反復する関手。
方針：零段は恒等、後続段では一段のセル付加を後合成する。
規約：対象ごとの反復を実際の関手として束ねる。使われ方：可算の置換図式。 -/
def hornCellStage : ℕ → (SSet.{u} ⥤ SSet.{u})
  | 0 => 𝟭 SSet.{u}
  | n + 1 => hornCellStage n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCellStep.{u}

/-- 概要：各反復段から次の段への自然な射。
方針：その段の関手で一段の付加の単位を前合成する。
規約：各対象で元の一段の単位となる。使われ方：反復図式の後続射。 -/
def hornCellStageMap (n : ℕ) : hornCellStage.{u} n ⟶ hornCellStage.{u} (n + 1) :=
  Functor.whiskerLeft (hornCellStage n) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCellStepUnit

/-- 概要：全ての反復段を関手圏の可算図式に束ねる。
方針：後続段の自然変換から自然数の半順序上の関手を作る。
規約：添字を AsSmall で単体集合と同じ宇宙へ持ち上げる。使われ方：反復の余極限。 -/
def hornCellSequence : AsSmall.{u} ℕ ⥤ SSet.{u} ⥤ SSet.{u} :=
  AsSmall.down ⋙ Functor.ofSequence hornCellStageMap

/-- 概要：ホーンセル付加を可算回反復した余極限関手。
方針：関手圏で反復図式の余極限を取る。
規約：Kan 性・弱同値性を定義に加えない。使われ方：連続な Kan 置換の候補。 -/
def continuousKanReplacement : SSet.{u} ⥤ SSet.{u} := colimit hornCellSequence.{u}

/-- 概要：元の対象から反復の余極限への自然な比較射。
方針：恒等関手である零段の余極限への包含を取る。
規約：元の対象を別の同型な対象へ置き換えない。使われ方：Kan 置換の単位。 -/
def continuousKanReplacementUnit : 𝟭 SSet.{u} ⟶ continuousKanReplacement.{u} :=
  colimit.ι hornCellSequence.{u} (AsSmall.up.obj 0)

/-- 概要：各有限反復段は filtered 余極限を保つ。
方針：一段の保存性と関手の合成で帰納する。
規約：同じ宇宙の小図式を扱う。使われ方：可算反復の余極限の連続性。 -/
instance hornCellStage_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} (hornCellStage.{u} n) := by
  induction n with
  | zero => change PreservesFilteredColimitsOfSize.{u, u} (𝟭 SSet.{u}); infer_instance
  | succ n ih =>
    change PreservesFilteredColimitsOfSize.{u, u} (hornCellStage.{u} n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCellStep.{u})
    infer_instance

/-- 概要：反復の余極限関手は filtered 余極限を保つ。
方針：各段の保存性を関手の余極限で保つ。
規約：保存性は具体的な反復から証明する。使われ方：有限部分複体への因子分解。 -/
instance continuousKanReplacement_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} continuousKanReplacement.{u} := by
  have : ∀ n, PreservesFilteredColimitsOfSize.{u, u} (hornCellSequence.{u}.obj n) := by
    intro n
    change PreservesFilteredColimitsOfSize.{u, u} (hornCellStage.{u} (AsSmall.down.obj n))
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.preservesFilteredColimits_colimit_of_pointwise hornCellSequence.{u}

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
