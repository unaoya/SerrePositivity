module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaUniversalDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCandidate

/-!
概要：通常の関手圏と comma の相対 join の図式の族との単体的比較。
方針：底で一度選んだ普遍図式への前合成を使う。
規約：右端の回収と標的の変更への自然性を厳密な等式で保つ。
使われ方：元の関手圏の相対制限へ写像空間の結果を戻すための族の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：元の関手の族を同じ普遍図式への後合成で comma の相対 join へ写す。
方針：固定した単体集合の射による前合成を使う。
規約：頂点だけでなく全次数の族を一つの単体写像で扱う。
使われ方：相対 Kan 図式の条件を関手圏全体で比較する。 -/
def kanLeftCommaUniversalFamily {K C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (D : SSet.{u}) :
    (ihom C).obj D ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C))).obj D :=
  (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ)).app D

/-- 概要：普遍図式へ移した族を右端へ制限すると元の族に厳密に戻る。
方針：前合成の合成公式に普遍図式の右端の恒等性を適用する。
規約：すべての次数での単体写像の等式。
使われ方：元の関手を保つ比較の切断。 -/
lemma kanLeftCommaUniversalFamily_inr {K C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (D : SSet.{u}) :
    kanLeftCommaUniversalFamily δ D ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C))).app D = 𝟙 _ := by
  rw [kanLeftCommaUniversalFamily, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram_inr, pre_id, NatTrans.id_app]

/-- 概要：普遍図式へ移した族の左端は元の図式を comma の射影で引き戻した族。
方針：前合成の合成公式と普遍図式の左端の式を使う。
規約：元の δ による制限をすべての次数で保持する。
使われ方：相対関手の制限の標的を比較する。 -/
lemma kanLeftCommaUniversalFamily_inl {K C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (D : SSet.{u}) :
    kanLeftCommaUniversalFamily δ D ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C))).app D =
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ)).app D := by
  rw [kanLeftCommaUniversalFamily, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram_inl]

/-- 概要：普遍図式による族の比較は標的の後合成に自然。
方針：内部 Hom の前合成と後合成の交換則を使う。
規約：U に充填性を要求しない。
使われ方：U による像も固定する相対制限の比較。 -/
lemma kanLeftCommaUniversalFamily_postcomp {K C D E : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (U : D ⟶ E) :
    kanLeftCommaUniversalFamily δ D ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C))).map U =
        (ihom C).map U ≫ kanLeftCommaUniversalFamily δ E :=
  pre_comm_ihom_map _ _

/-- 概要：普遍図式に後合成した図式の右端の候補は元の関手。
方針：底での右端の恒等性へ元の関手を後合成する。
規約：候補は同型ではなく厳密に同じ関手となる。
使われ方：comma 上の局所判定を元の F へ戻す。 -/
lemma kanLeftCommaUniversalFamily_candidate {K C D : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F) = F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram_inr,
    Category.id_comp]

/-- 概要：普遍図式に後合成した図式の左端は δ による元の制限を保つ。
方針：底での左端の等式へ元の関手を後合成する。
規約：候補変換の構成に渡す厳密な等式。
使われ方：元の関手の制限上の指定変換を抽出する。 -/
lemma kanLeftCommaUniversalFamily_diagram {K C D : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ (δ ≫ F) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram_inl, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
