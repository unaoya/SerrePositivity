module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionHomSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentPiZero
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingHomComparison

/-!
概要：部分余極限の実際の比較辺を含む族で、余錐の制限の Hom 比較を全単体で計算する。
方針：付加で構成した余錐圏の辺を正規化した制限の終点で表示し、始対象の自然性を適用する。
規約：共通部分と元の図式の指定余錐は余極限。比較辺は既存の付加で選んだものを保持する。
使われ方：部分余極限対象の span の Hom 図式と、元の余錐空間の引き戻しの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} {p : A ⟶ X}
  (c : JoinCocone p) (hc : IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F)

/-- 付加による比較辺を、正規化した制限の像を終点とする辺として表す。 -/
def colimitAttachmentRestrictionEdge :
    (sliceUnder p).Edge c ((normalizedCoconeRestriction F i hi).app (Opposite.op ⦋0⦌) d) := by
  let e := colimitAttachmentCoconeEdge c hc i F hi d
  refine ⟨e.edge, e.src_eq, e.tgt_eq.trans ?_⟩
  cases hi
  rfl

/-- 余錐圏の比較辺の底への像は、元の実際の付加比較辺を保つ。 -/
lemma colimitAttachmentRestrictionEdge_projection :
    ((colimitAttachmentRestrictionEdge c hc i F hi d).map (sliceUnderProjection p)).edge =
      (colimitAttachmentApexEdge c hc i F hi d).edge :=
  (coconeComparisonEdge_projection c (colimitAttachmentComparison c hc i F hi d)).trans
    (colimitAttachmentComparison_leg_edge c hc i F hi d)

/-- 比較辺の底の図式も、構成済みの実際の付加比較辺の Yoneda 表示そのもの。 -/
lemma colimitAttachmentRestrictionEdge_projection_map :
    SSet.yonedaEquiv.symm (colimitAttachmentRestrictionEdge c hc i F hi d).edge ≫
        sliceUnderProjection p =
      SSet.yonedaEquiv.symm (colimitAttachmentApexEdge c hc i F hi d).edge := by
  rw [SSet.yonedaEquiv_symm_comp]
  exact congrArg SSet.yonedaEquiv.symm (colimitAttachmentRestrictionEdge_projection c hc i F hi d)

variable [Quasicategory X] (hd : IsColimitCone d) (y : X _⦋0⦌)

/-- 実際の比較辺の底の合成三角形で計算する、元の余錐空間から部分余極限の Hom への族。 -/
def colimitAttachmentRestrictionHomFamily :
    coconeMappingSpace F y ⟶ pinchedHomLeft c.vertex y :=
  initialRestrictionEdgeHomFamily (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y

/-- 余錐の制限と始対象による Hom 比較は、付加した実際の辺の族と全単体でホモトピック。 -/
lemma coconeMappingSpaceHomComparison_restrict_homotopy :
    Nonempty (SSet.Homotopy
      (normalizedCoconeRestrictionFiber F i hi y ≫ coconeMappingSpaceHomComparison c hc y)
      (colimitAttachmentRestrictionHomFamily c hc i F hi d hd y)) :=
  initialRestrictionHomComparison_homotopy (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

/-- 付加で選んだ実際の比較辺による、二つの部分余極限頂点の左 Hom の前合成。 -/
def colimitAttachmentHomPrecomposition :
    pinchedHomLeft d.vertex y ⟶ pinchedHomLeft c.vertex y :=
  initialRestrictionHomPrecomposition (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d (colimitAttachmentRestrictionEdge c hc i F hi d) y

/-- 部分余錐の制限の Hom 比較は、付加で選んだ実際の比較辺の前合成と全単体で可換。 -/
lemma coconeMappingSpaceHomComparison_restrict_square :
    Nonempty (SSet.Homotopy
      (normalizedCoconeRestrictionFiber F i hi y ≫ coconeMappingSpaceHomComparison c hc y)
      (coconeMappingSpaceHomComparison d hd y ≫
        colimitAttachmentHomPrecomposition c hc i F hi d y)) :=
  initialRestrictionHomComparison_square (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

end
end SerrePositivity.InfinityCategories.HomotopyLimits
