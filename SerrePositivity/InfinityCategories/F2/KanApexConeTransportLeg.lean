module

public import SerrePositivity.InfinityCategories.F2.KanApexConeTransportEdges
public import SerrePositivity.InfinityCategories.F2.EdgeSquareTransport
public import SerrePositivity.InfinityCategories.F2.SpaceHomotopyClasses

/-!
概要：元の Kan 射による頂点輸送の各脚を、元の射と比較先の脚の合成へ比較する。
方針：全錐の自然性の四辺を実際の coherent 辺へ移し、図式の恒等辺を消去する。
規約：元の射と二つの頂点を保持。使われ方：一般 coherent filtered 余極限後の脚。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {D : I ⥤ KanObject.{u}}
  (d : JoinCone (kanDiagramCoherentNerve D))
  {K L : KanObject.{u}} (a : K ⟶ L) {v : SpaceInfinity.{u} _⦋0⦌}
  (t : SpecifiedApexLimitConeTransport d (SSet.yonedaEquiv.symm v)
    (edgeApexPrism (coherentNerveEdge a)))
  (hv : v = coherentNerveVertex K)

/-- 元の始域を頂点とする輸送後の脚を、同じ Kan 対象間の射へ戻す。 -/
def kanApexConeTransportLeg (i : I) : K ⟶ D.obj i :=
  kanNativeConeLeg t.cone K (kanApexConeTransport_vertex d a t hv) i

/-- 輸送後の脚は、元の比較射と元の比較先の脚の合成にホモトピック。 -/
lemma kanApexConeTransportLeg_comparison (hd : d.vertex = coherentNerveVertex L) (i : I) :
    Nonempty (SSet.Homotopy (kanApexConeTransportLeg d a t hv i)
      (a ≫ kanNativeConeLeg d L hd i)) := by
  let j := ULift.up.{u + 1} (ComposableArrows.mk₀ i)
  let V := D.obj i
  have hdi := (kanDiagramCoherentNerve_vertex D i).trans (spaceInfinityVertex_eq_coherent _)
  have hr : (coneHomotopyDiagramEdge t.homotopy j).edge =
      (coherentNerveEdge (𝟙 V)).edge := by
    rw [kanApexConeTransport_diagramEdge]
    calc
      _ = PinchedHom.constant (coherentNerveVertex V) 1 :=
        congrArg (fun x => PinchedHom.constant x 1) hdi
      _ = _ := by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl
  have hs := homMk_square_transport (nativeConeLeg t.cone j)
    (coneHomotopyDiagramEdge t.homotopy j) (coneHomotopyApexEdge t.homotopy)
    (nativeConeLeg d j)
    (coherentNerveEdge (kanApexConeTransportLeg d a t hv i)).toTruncated
    (coherentNerveEdge (𝟙 V)).toTruncated (coherentNerveEdge a).toTruncated
    (coherentNerveEdge (kanNativeConeLeg d L hd i)).toTruncated
    (coneHomotopy_leg_naturality t.homotopy j)
    (kanApexConeTransport_vertex d a t hv) hdi hd hdi
    (kanNativeConeLeg_edge _ _ _ i).symm hr (kanApexConeTransport_apexEdge d a t)
    (kanNativeConeLeg_edge d L hd i).symm
  have hid : SSet.Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (𝟙 V)).toTruncated = 𝟙 _ := by
    rw [coherentNerveEdge_id, SSet.Edge.toTruncated_id,
      SSet.Truncated.HomotopyCategory.homMk_id]
  rw [hid, Category.comp_id] at hs
  apply spaceInfinity_homotopy_of_homMk_eq
  exact hs.trans (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct a (kanNativeConeLeg d L hd i)).toTruncated)

end SerrePositivity.InfinityCategories.F2
