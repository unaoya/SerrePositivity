module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreComparisonEdgeCoordinates

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionCoreComparisonEdge_homMk_of_coneEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e)
    (a : Truncated.Edge (X := (truncation 2).obj (sliceOver
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
      (excisionCorePuncturedOuterCone (excisionCorePuncturedLimitCone F d hd)) e) :
    let q := sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))
    let hv : (excisionCorePuncturedOuterCone
        (excisionCorePuncturedLimitCone F d hd)).vertex = d.vertex :=
      (excisionCorePuncturedOuterCone_vertex _).trans
        (excisionCorePuncturedLimitCone_vertex F d hd)
    Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map q)) =
      eqToHom (congrArg (fun v ↦ (HomotopyCategory.mk v : hoFunctor.obj X)) hv) ≫
        Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge F d hd e he) := by
  intro q hv
  have ha : Truncated.HomotopyCategory.homMk a =
      Truncated.HomotopyCategory.homMk (excisionCoreComparisonConeEdge F d hd e he) :=
    he.isTerminalHo.hom_ext _ _
  have h := congrArg ((Truncated.mapHomotopyCategory ((truncation 2).map q)).map) ha
  simp only [Truncated.mapHomotopyCategory_homMk] at h
  exact h.trans (homMk_eqToHom_comp_of_edge_eq _ _ hv
    (excisionCoreComparisonEdge_edge F d hd e he).symm)

end SerrePositivity.InfinityCategories
