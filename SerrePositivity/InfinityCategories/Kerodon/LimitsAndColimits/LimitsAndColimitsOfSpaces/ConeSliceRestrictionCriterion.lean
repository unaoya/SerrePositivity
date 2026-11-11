module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeIteratedSliceIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeSpanLimitCriterion

/-!
概要：native な極限錐を錐の図式上の slice から元の図式の slice への制限で検出する。
方針：比較 span の中間空間の厳密な同型と実際の評価の可換式で従来の判定を移す。
規約：全ての coherent な錐と全ての頂点を扱い、strict な錐に制限しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の切断の制限による極限判定への接続。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：錐の図式上の slice の頂点 fiber を元の図式の slice の頂点 fiber へ制限する。
方針：底 X の上の標準制限を同じ頂点 x の fiber へ移す。
規約：射の定義には充填性を要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の native な極限判定の実際の制限射。 -/
def coneSliceRestrictionFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection c.val) x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSliceOverRestriction c) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSliceOverRestriction_projection c) x

/-- 概要：native な比較 span の評価が同値であることと slice の制限が同値であることは同値。
方針：中間空間の厳密な同型で合成を分解し、Kan 空間の二対三則を使う。
規約：前提は X の quasicategory 性のみ。
使われ方：HTT 4.2.4.1 の選択付きの比較を介さない極限判定の移送。 -/
lemma coneSliceRestrictionFiberMap_homotopyEquivalence_iff {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coneSliceRestrictionFiberMap c x) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection c.val) x
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneMappingTotalIso c x)).isQCatEquivalence
  have hcomp : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneMappingTotalIso c x).hom ≫ coneSliceRestrictionFiberMap c x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneMappingTotalIso_evaluation c x
  constructor
  · intro h
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneMappingTotalIso c x).hom ≫ coneSliceRestrictionFiberMap c x) := by
      rw [hcomp]
      exact h.isQCatEquivalence
    exact (he.cancel_left hc).isSimplicialHomotopyEquivalence
  · intro h
    rw [← hcomp]
    exact (he.comp h.isQCatEquivalence).isSimplicialHomotopyEquivalence

/-- 概要：coherent な錐の極限性は全頂点での slice の制限のホモトピー同値性で検出できる。
方針：A3d に基づく native な比較 span の極限判定を、実際の制限射へ移す。
規約：K は任意の単体集合。豊穣 Hom の比較との接続は別途必要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の錐の図式上の切断の制限を使う比較の入力。 -/
lemma isLimitCone_iff_coneSliceRestrictionFiberMap_homotopyEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coneSliceRestrictionFiberMap c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_mappingEvaluation_homotopyEquivalence]
  exact forall_congr' (fun x ↦ coneSliceRestrictionFiberMap_homotopyEquivalence_iff c x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
