module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionHomSquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentPiZero
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingHomComparison

/-!
概要：部分余極限の実際の比較辺を含む族で、余錐の制限の Hom 比較を全単体で計算する。
方針：付加で構成した余錐圏の辺を正規化した制限の終点で表示し、始対象の自然性を適用する。
規約：共通部分と元の図式の指定余錐は余極限。比較辺は既存の付加で選んだものを保持する。
使われ方：部分余極限対象の span の Hom 図式と、元の余錐空間の引き戻しの比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {A C X : SSet.{u}} {p : A ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)

/-- 付加による比較辺を、正規化した制限の像を終点とする辺として表す。 -/
def colimitAttachmentRestrictionEdge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).Edge c ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F i hi).app (Opposite.op ⦋0⦌) d) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentCoconeEdge c hc i F hi d
  refine ⟨e.edge, e.src_eq, e.tgt_eq.trans ?_⟩
  cases hi
  rfl

/-- 余錐圏の比較辺の底への像は、元の実際の付加比較辺を保つ。 -/
lemma colimitAttachmentRestrictionEdge_projection :
    ((colimitAttachmentRestrictionEdge c hc i F hi d).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi d).edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeComparisonEdge_projection c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentComparison c hc i F hi d)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentComparison_leg_edge c hc i F hi d)

/-- 比較辺の底の図式も、構成済みの実際の付加比較辺の Yoneda 表示そのもの。 -/
lemma colimitAttachmentRestrictionEdge_projection_map :
    SSet.yonedaEquiv.symm (colimitAttachmentRestrictionEdge c hc i F hi d).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi d).edge := by
  rw [SSet.yonedaEquiv_symm_comp]
  exact congrArg SSet.yonedaEquiv.symm (colimitAttachmentRestrictionEdge_projection c hc i F hi d)

variable [Quasicategory X] (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) (y : X _⦋0⦌)

/-- 実際の比較辺の底の合成三角形で計算する、元の余錐空間から部分余極限の Hom への族。 -/
def colimitAttachmentRestrictionHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeHomFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y

/-- 余錐の制限と始対象による Hom 比較は、付加した実際の辺の族と全単体でホモトピック。 -/
lemma coconeMappingSpaceHomComparison_restrict_homotopy :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison c hc y)
      (colimitAttachmentRestrictionHomFamily c hc i F hi d hd y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomComparison_homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

/-- 付加で選んだ実際の比較辺による、二つの部分余極限頂点の左 Hom の前合成。 -/
def colimitAttachmentHomPrecomposition :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft d.vertex y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft c.vertex y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection F i hi)
    d (colimitAttachmentRestrictionEdge c hc i F hi d) y

/-- 部分余錐の制限の Hom 比較は、付加で選んだ実際の比較辺の前合成と全単体で可換。 -/
lemma coconeMappingSpaceHomComparison_restrict_square :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison c hc y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison d hd y ≫
        colimitAttachmentHomPrecomposition c hc i F hi d y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomComparison_square (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
