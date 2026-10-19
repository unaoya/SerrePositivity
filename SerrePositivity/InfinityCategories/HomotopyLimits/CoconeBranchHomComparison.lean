module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentPointHom

/-!
概要：任意の余錐の全 Hom の族の枝への制限を、指定した頂点の辺そのものの前合成と結ぶ。
方針：余錐圏の比較辺の底を厳密に同定し、任意の点の Hom の制限比較へ代入する。
規約：元の余錐の余極限性は不要。使われ方：貼り合わせた余錐と span の実際の脚の全 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K L X : SSet.{u}} [Quasicategory X] {F : K ⟶ X} {G : L ⟶ X}
  (c : JoinCocone G) (d : JoinCocone F) (e : X.Edge c.vertex d.vertex) (y : X _⦋0⦌)

/-- 指定した余錐頂点間の実際の辺による、両頂点の全左 Hom の前合成。 -/
def coconeApexHomPrecomposition : pinchedHomLeft d.vertex y ⟶ pinchedHomLeft c.vertex y :=
  (leftFibrationInitialBaseIso (sliceUnderProjection F) d y).inv ≫
    cosliceEdgeFiberPrecomposition (SSet.yonedaEquiv.symm e.edge)
      (coconeVertexDiagram c) (coconeVertexDiagram d)
      (by rw [coconeVertexDiagram_eq]; exact e.δ_one_yonedaEquiv_symm)
      (by rw [coconeVertexDiagram_eq]; exact e.δ_zero_yonedaEquiv_symm) y ≫
    (leftFibrationInitialBaseIso (sliceUnderProjection G) c y).hom

variable (i : L ⟶ K) (hi : i ≫ F = G)
  (k : (sliceUnder G).Edge c ((normalizedCoconeRestriction F i hi).app (Opposite.op ⦋0⦌) d))
  (hk : (k.map (sliceUnderProjection G)).edge = e.edge)

include hk in
/-- 余錐圏の比較辺が指定した頂点の辺を被覆すれば、その前合成は指定した辺の前合成そのもの。 -/
lemma coconeBranchHomPrecomposition_eq :
    initialRestrictionHomPrecomposition (sliceUnderProjection F) (sliceUnderProjection G)
        (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
        d k y = coconeApexHomPrecomposition c d e y := by
  have hh : SSet.yonedaEquiv.symm k.edge ≫ sliceUnderProjection G =
      SSet.yonedaEquiv.symm e.edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm hk
  simp only [initialRestrictionHomPrecomposition, coconeApexHomPrecomposition, hh,
    coconeVertexDiagram]

include hk in
/-- 任意の余錐の全 Hom の族の枝への制限は、実際の頂点の辺での前合成とホモトピック。 -/
lemma coconePointHomFamily_branch_homotopy (hc : IsColimitCone c) :
    Nonempty (SSet.Homotopy
      ((coconePointHomFamily d y ≫ normalizedCoconeRestrictionFiber F i hi y) ≫
        coconeMappingSpaceHomComparison c hc y)
      (coconeApexHomPrecomposition c d e y)) := by
  have H := pointHomFamily_restriction_comparison_homotopy
    (sliceUnderProjection F) (sliceUnderProjection G)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi) d k y hc
  rwa [coconeBranchHomPrecomposition_eq c d e y i hi k hk] at H

end
end SerrePositivity.InfinityCategories.HomotopyLimits
