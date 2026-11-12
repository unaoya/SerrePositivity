module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionConeEquivalence

/-!
概要：coslice の切断空間を終域とする表現可能な ∞ 極限判定。
方針：right fibration の実際の比較の終域を、固定頂点の錐と切断空間の同値で移す。
規約：比較は選んだ逆と span の切断を含み、豊穣 Hom からの q_x との一致は別に証明する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断模型への接続。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：底の pinched Hom から coherent な錐の coslice の切断空間への表現可能な比較。
方針：right fibration の比較と錐の頂点 fiber から切断空間への同値を合成する。
規約：同値の逆と span の切断の選択を含み、その自然性は主張しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の ∞ 極限の切断模型による検出。 -/
noncomputable def coneSectionHomComparison {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x c.vertex ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationHomComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberSectionEquivalence p x).hom

/-- 概要：切断空間への表現可能な比較の同値性は錐の頂点 fiber への比較の同値性と同値。
方針：終域の模型の同値性と二対三則を使う。
規約：任意の図式と任意の coherent な錐を扱う。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の表現可能な極限判定の終域を切断空間へ移す。 -/
lemma coneSectionHomComparison_homotopyEquivalence_iff {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coneSectionHomComparison c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationHomComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberSectionEquivalence p x).isQCatEquivalence
  constructor
  · intro h
    exact (he.cancel_right h.isQCatEquivalence).isSimplicialHomotopyEquivalence
  · intro h
    exact (h.isQCatEquivalence.comp he).isSimplicialHomotopyEquivalence

/-- 概要：錐の極限性は全ての頂点での coslice の切断空間への比較のホモトピー同値性で検出できる。
方針：既存の native な表現可能な極限判定を、終域の模型の同値で移す。
規約：K は任意。通常の圏から来る strict な錐だけに制限しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の主比較の切断側の判定。 -/
lemma isLimitCone_iff_coneSectionHomComparison_homotopyEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coneSectionHomComparison c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_rightFibrationHomComparison_homotopyEquivalence]
  apply forall_congr'
  intro x
  exact (coneSectionHomComparison_homotopyEquivalence_iff c x).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
