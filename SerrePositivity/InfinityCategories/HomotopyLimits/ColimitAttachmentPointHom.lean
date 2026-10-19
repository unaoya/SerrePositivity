module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomCospanIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitApexSpan

/-!
概要：部分余極限の左 Hom の cospan を、実際の付加比較辺の点 coslice の cospan と同型にする。
方針：既存の始対象の底の fiber 同型を三成分に置き、前合成の定義の共役を消去する。
規約：同型は全単体で厳密に自然。使われ方：元の余錐空間と native な span の余錐空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 余錐の頂点を、その実際の coslice の射影を通る点図式として表示する。 -/
def coconeVertexDiagram {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    (Δ[0] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm c ≫ sliceUnderProjection p

/-- coslice の射影を通る表示は、元の余錐頂点の Yoneda 表示と一致。 -/
lemma coconeVertexDiagram_eq {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    coconeVertexDiagram c = SSet.yonedaEquiv.symm c.vertex := by
  rw [coconeVertexDiagram, SSet.yonedaEquiv_symm_comp]
  rfl

variable {A C X : SSet.{u}} {q : A ⟶ X}
  (c : JoinCocone q) (hc : IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = q) (d : JoinCocone F)

/-- 実際の余錐圏の比較辺を底へ射影した点 Hom の前合成の辺。 -/
def colimitAttachmentPointEdge : (Δ[1] : SSet.{u}) ⟶ X :=
  SSet.yonedaEquiv.symm (colimitAttachmentRestrictionEdge c hc i F hi d).edge ≫
    sliceUnderProjection q

/-- 点 Hom の辺は元の付加比較辺そのもの。 -/
lemma colimitAttachmentPointEdge_eq :
    colimitAttachmentPointEdge c hc i F hi d =
      SSet.yonedaEquiv.symm (colimitAttachmentApexEdge c hc i F hi d).edge :=
  colimitAttachmentRestrictionEdge_projection_map c hc i F hi d

/-- 前合成の辺の始点は共通部分の実際の余錐頂点。 -/
lemma colimitAttachmentPointEdge_source :
    stdSimplex.δ (1 : Fin 2) ≫ colimitAttachmentPointEdge c hc i F hi d =
      coconeVertexDiagram c := by
  rw [colimitAttachmentPointEdge, ← Category.assoc,
    (colimitAttachmentRestrictionEdge c hc i F hi d).δ_one_yonedaEquiv_symm]
  rfl

/-- 前合成の辺の終点は部分図式の実際の余錐頂点。 -/
lemma colimitAttachmentPointEdge_target :
    stdSimplex.δ (0 : Fin 2) ≫ colimitAttachmentPointEdge c hc i F hi d =
      coconeVertexDiagram d :=
  (initialRestrictionEdgeBase_eq (sliceUnderProjection F) (sliceUnderProjection q)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d (colimitAttachmentRestrictionEdge c hc i F hi d)).symm

variable [Quasicategory X] (y : X _⦋0⦌)

/-- 底の点 Hom の前合成は、左 pinched Hom の前合成と厳密な同型を通して可換。 -/
lemma colimitAttachmentPointHom_square :
    cosliceEdgeFiberPrecomposition (colimitAttachmentPointEdge c hc i F hi d)
        (coconeVertexDiagram c) (coconeVertexDiagram d)
        (colimitAttachmentPointEdge_source c hc i F hi d)
        (colimitAttachmentPointEdge_target c hc i F hi d) y ≫
        (leftFibrationInitialBaseIso (sliceUnderProjection q) c y).hom =
      (leftFibrationInitialBaseIso (sliceUnderProjection F) d y).hom ≫
        colimitAttachmentHomPrecomposition c hc i F hi d y := by
  simp only [colimitAttachmentHomPrecomposition, initialRestrictionHomPrecomposition,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
