module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement

/-!
概要：具体的な連続 Kan 置換への単位は弱ホモトピー同値。
方針：証明済みの anodyne 性から Kan 標的への前合成のホモトピー同値を使う。
規約：既存の N の Kan 標的の比較は読み取り専用で再利用する。
使われ方：有限部分での収縮を連続 Kan 置換後に移す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：連続 Kan 置換への元の単位は全ての対象で弱ホモトピー同値。
方針：Kan 標的への前合成のホモトピー同値から連結成分の全単射を取る。
規約：X 自体の Kan 性も quasicategory 性も不要。
使われ方：一般の filtered ∞ 圏の弱可縮性を Kan 複体で判定する。 -/
lemma continuousKanReplacementUnit_isWeakHomotopyEquivalence (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) := by
  intro Z _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne X) Z).mapPiZero_bijective

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
