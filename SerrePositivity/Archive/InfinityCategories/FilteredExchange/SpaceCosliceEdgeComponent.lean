module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CosliceComparisonVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexSourceCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges

/-!
概要：元の Kan 射の標準 Hom 比較の零成分を、同じ実 coslice 頂点として読む。
方針：既存の辺の回収式を join 座標へ移し、座標の単射性で比較する。
規約：元の Kan 射と実一次単体を保持。使われ方：全 pointed 族の三頂点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の Kan 射の標準の全 Hom 比較の零成分を、元の実 coslice 頂点で読む。 -/
def coherentCosliceEdgeComponent {K L : KanObject.{u}} (f : K ⟶ L) :
    (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K))) _⦋0⦌ :=
  (coherentCosliceFiberComparison K L ≫ vertexFiberι
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
      (coherentNerveVertex L)).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K L f)))

/-- 元の標準成分の join 座標は、元の同じ Kan 射の coherent 辺。 -/
lemma coherentCosliceEdgeComponent_coordinates {K L : KanObject.{u}} (f : K ⟶ L) :
    coherentCosliceSourceSimplex K (coherentCosliceEdgeComponent f) =
      (coherentNerveEdge f).edge := by
  have h := congrArg SSet.Edge.edge
    (coherentCosliceFiberComparison_vertex_edge K L (SimplicialCategory.homEquiv' K L f))
  have hi : leftPointStdSimplexIso.{u + 1} 0 = joinStdSimplexIso 0 0 := by
    apply Iso.ext
    rfl
  unfold coherentCosliceSourceSimplex coherentCosliceEdgeComponent
  rw [hi]
  let t := (coherentCosliceFiberComparison K L).app (Opposite.op ⦋0⦌)
    (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K L f)))
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ t.val.val) =
    (coherentNerveEdge ((SimplicialCategory.homEquiv' K L).symm
      (SimplicialCategory.homEquiv' K L f))).edge at h
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ t.val.val) = _
  simpa only [Equiv.symm_apply_apply] using h

/-- 元の実 Space 辺の Hom 成分を使うと、join 座標は同じ実一次単体そのもの。 -/
lemma coherentCosliceEdgeComponent_space_coordinates (e : SpaceInfinity.{u} _⦋1⦌) :
    coherentCosliceSourceSimplex (e.obj ⟨ULift.up 0⟩)
      (coherentCosliceEdgeComponent (coherentEdgeHom e)) = e :=
  (coherentCosliceEdgeComponent_coordinates (coherentEdgeHom e)).trans (coherentEdge_recover e)

/-- 実 coslice の同じ join 座標への移送は、全単体で単射。 -/
lemma spaceCosliceSourceSimplex_injective (K : KanObject.{u}) (n : ℕ) :
    Function.Injective (coherentCosliceSourceSimplex K (n := n)) := by
  intro a b h
  apply Subtype.ext
  apply (cancel_epi (leftPointStdSimplexIso n).inv).mp
  exact SSet.yonedaEquiv.injective h

end SerrePositivity.InfinityCategories.F2
