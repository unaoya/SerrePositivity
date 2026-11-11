module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HornCellData

/-!
概要：全てのホーンに対するセルを一度に付加する具体的な関手。
方針：関手圏で評価射と境界射の pushout を取る。
規約：まだ Kan 置換ではなく一回のセル付加。反復と連続性は別に証明する。
使われ方：filtered 余極限と可換な Kan 置換の明示的な構成。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：各対象に全ホーンのセルを一段付加する関手。
方針：全てのホーンのコピーの評価と境界射を関手圏で押し出す。
規約：対象ごとの選択ではなく実際の関手。使われ方：Kan 置換の可算反復。 -/
def hornCellStep : SSet.{u} ⥤ SSet.{u} :=
  pushout _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u}

/-- 概要：元の対象から一段のホーンセル付加への自然な射。
方針：pushout の元の対象側の包含を取る。
規約：全ての対象に自然。使われ方：反復図式の遷移射。 -/
def hornCellStepUnit : 𝟭 SSet.{u} ⟶ hornCellStep.{u} :=
  pushout.inl _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u}

/-- 概要：付加した全てのセルのコピーから一段の付加への射。
方針：pushout のセル側の包含を取る。
規約：各ホーンの終域をそのセルとして含める。使われ方：指定ホーンの充填。 -/
def hornCellStepCells : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornTargetCopies.{u} ⟶ hornCellStep.{u} :=
  pushout.inr _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u}

/-- 概要：付加したセルの境界は元の対象への評価と一致する。
方針：関手圏の pushout の可換性を読む。
規約：等式は自然変換全体の厳密な等式。使われ方：境界を固定するホーンの充填。 -/
lemma hornCellStep_condition :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u} ≫ hornCellStepUnit = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary ≫ hornCellStepCells :=
  pushout.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u}) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u})

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
