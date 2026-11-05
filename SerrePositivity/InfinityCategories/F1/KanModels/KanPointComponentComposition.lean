module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceTransportPointHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedReverseFiberVertices

/-! # 同じ Kan 点の矢印と coherent な比較成分の合成を、元の点の実像として読む -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.KanModels
open SerrePositivity.KST.Fibration

/-- 元の Kan 点の pointed-space 表示は、同じ点の Yoneda 射の coherent 辺そのもの。 -/
theorem pointedKanPointEdge_eq (K : KanObject.{u}) (v : K.obj _⦋0⦌) :
    (coherentNerveEdge (show pointKanObject ⟶ K from SSet.yonedaEquiv.symm v)).edge =
      (cosliceFiberVertexToEdge ((pointedSpaceFiberVertexEquiv K).symm v)).edge := by
  let s := (pointedSpaceFiberVertexEquiv K).symm v
  let e := (cosliceFiberVertexToEdge s).ofEq
    (spaceInfinityVertex_eq_coherent pointKanObject) (spaceInfinityVertex_eq_coherent K)
  have hp : SSet.yonedaEquiv (show pointKanObject ⟶ K from
      coherentNerveEdgeToHom e) = v :=
    (pointedSpaceFiberVertexEquiv_edge K s).symm.trans
      ((pointedSpaceFiberVertexEquiv K).apply_symm_apply v)
  have hm : coherentNerveEdgeToHom e = (show pointKanObject ⟶ K from
      SSet.yonedaEquiv.symm v) := by
    have h := congrArg SSet.yonedaEquiv.symm hp
    simpa only [Equiv.symm_apply_apply] using h
  have he := congrArg SSet.Edge.edge (coherentNerveEdge_hom e)
  rw [hm] at he
  exact he

/-- 元の Kan 点の射と同じ coherent 成分辺の合成は、指定した写像による同じ点の実像の射。 -/
theorem kanPointHom_comp_of_edge {K L : KanObject.{u}} (f : K ⟶ L)
    (e : SpaceInfinity.Edge (spaceInfinityVertex K) (spaceInfinityVertex L))
    (he : e.edge = (coherentNerveEdge f).edge) (v : K.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv K).symm v) ≫
      Truncated.HomotopyCategory.homMk e.toTruncated =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv L).symm
        (f.app (Opposite.op ⦋0⦌) v)) := by
  let p : pointKanObject ⟶ K := SSet.yonedaEquiv.symm v
  let t := coherentNerveCompStruct p f
  have hp : p ≫ f = (show pointKanObject ⟶ L from
      SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) v)) :=
    SSet.yonedaEquiv_symm_comp v f
  have T : SSet.Edge.CompStruct
      (cosliceFiberVertexToEdge ((pointedSpaceFiberVertexEquiv K).symm v)) e
      (cosliceFiberVertexToEdge ((pointedSpaceFiberVertexEquiv L).symm
        (f.app (Opposite.op ⦋0⦌) v))) := by
    refine ⟨t.simplex, ?_, ?_, ?_⟩
    · exact t.d₂.trans (_root_.SerrePositivity.InfinityCategories.F1.KanModels.pointedKanPointEdge_eq K v)
    · exact t.d₀.trans he.symm
    · have ht : (coherentNerveEdge (p ≫ f)).edge =
          (coherentNerveEdge (show pointKanObject ⟶ L from
            SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) v))).edge :=
        congrArg (fun m : pointKanObject ⟶ L => (coherentNerveEdge m).edge) hp
      exact t.d₁.trans (ht.trans (_root_.SerrePositivity.InfinityCategories.F1.KanModels.pointedKanPointEdge_eq L _))
  exact Truncated.HomotopyCategory.homMk_comp_homMk T.toTruncated

end SerrePositivity.InfinityCategories.F1.KanModels

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanPointHom_comp_of_edge := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanPointHom_comp_of_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedKanPointEdge_eq := _root_.SerrePositivity.InfinityCategories.F1.KanModels.pointedKanPointEdge_eq
