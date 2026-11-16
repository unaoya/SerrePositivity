module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiberEdgeProjectedArrow
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.ArrowMiddleIdentity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HomSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHomComposition

/-!
概要：同じ両端固定のtwisted Hom内の辺・頂点同型は、元の矢印の類を保持する。
方針：元の左右の定値射影を恒等射へ合わせ、同じ三辺の合成則へ適用する。
規約：元の点・元の辺・元の射影を使う。
使われ方：元のcoslice比較の同じ単位三角形を通す。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 同じ両端固定のHom空間内の元の辺は、元の矢印のArrowの類を保持する。 -/
lemma twistedArrowHomSpace_edge_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (e : SSet.Edge v w) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val)) := by
  let k := e.map (vertexFiberι (twistedArrowProjection C) (SSet.opObjEquiv.symm x, y))
  have hl : Arrow.mk (HomotopyCategory.homMk (k.map (edgewiseLeft C))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (SSet.opObjEquiv.symm x))) := by
    have hh := congrArg (fun f : TwistedArrow C ⟶ C.op =>
      Arrow.mk (HomotopyCategory.homMk (k.map f))) (twistedArrowProjection_fst C)
    exact hh.symm.trans (vertexFiber_edge_projected_arrow (twistedArrowProjection C) (fst C.op C) e)
  have hr : Arrow.mk (HomotopyCategory.homMk (k.map (edgewiseRight C))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk y)) := by
    have hh := congrArg (fun f : TwistedArrow C ⟶ C =>
      Arrow.mk (HomotopyCategory.homMk (k.map f))) (twistedArrowProjection_snd C)
    exact hh.symm.trans (vertexFiber_edge_projected_arrow (twistedArrowProjection C) (snd C.op C) e)
  have hl' := congrArg (fun z : Arrow (HomotopyCategory C.op) =>
    Arrow.mk (((homotopyOppositeEquivalence C).functor.map z.hom).unop)) hl
  simp only [Arrow.mk_hom] at hl'
  have hid := congrArg (fun f => Arrow.mk f.unop)
    ((homotopyOppositeEquivalence C).functor.map_id
      (HomotopyCategory.mk (SSet.opObjEquiv.symm x)))
  simp only [CategoryTheory.unop_id] at hid
  have hp := hl'.trans hid
  have hc := twistedArrowHom_composition (HomotopyCategory.homMk k)
  simp only [SSet.mapHomotopyCategory_map_homMk] at hc
  exact arrow_middle_eq_of_outer_identity_arrows _ _ _ _ hp hr hc

/-- 同じ両端固定のHom空間内の元の頂点同型は、元の矢印のArrowの類を保持する。 -/
lemma twistedArrowHomSpace_vertexIso_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (e : VertexIso v w) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val)) := by
  obtain ⟨l, _⟩ := homotopyCategory_homMk_surjective v w e.hom
  exact twistedArrowHomSpace_edge_arrow_eq (SSet.Edge.ofTruncated l)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
