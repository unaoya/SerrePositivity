module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowVertexEdgeNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberVertices

/-!
概要：元のcoslice比較の零単体が表す辺は、同じcoslice点の元の辺。
方針：零次元のcollapseを元の重みの同型に合わせ、同じ逆則を適用する。
規約：対象と元の比較・元の点・元の辺を保持し、quasicategory性は仮定しない。
使われ方：元のnative単位の辺の類を、同じHom空間の点の比較へ戻す。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 元の零次元のcollapseは、同じ反対零単体の同型のjoin。 -/
lemma cosliceEdgewiseCollapse_zero :
    cosliceEdgewiseCollapse.{u} ⦋0⦌ =
      (joinIso (stdSimplex.opIso ⦋0⦌) (Iso.refl (Δ[0] : SSet.{u}))).hom := by
  change joinMap (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (𝟙 _) =
    joinMap (stdSimplex.opIso ⦋0⦌).hom (𝟙 _)
  congr 1
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply stdSimplex.ext
  intro a
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- 元の零次元の重みの逆と同じcollapseの合成は、元のjoinの標準同型の逆。 -/
lemma edgewiseWeightIso_zero_inv_comp_cosliceCollapse :
    (edgewiseWeightIso.{u} 0).inv ≫ cosliceEdgewiseCollapse ⦋0⦌ =
      (joinStdSimplexIso 0 0).inv := by
  change ((joinStdSimplexIso 0 0).inv ≫
    (joinIso (stdSimplex.opIso ⦋0⦌) (Iso.refl (Δ[0] : SSet.{u}))).inv) ≫
      cosliceEdgewiseCollapse ⦋0⦌ = _
  rw [Category.assoc, cosliceEdgewiseCollapse_zero, Iso.inv_hom_id, Category.comp_id]

/-- 元のcoslice比較の同じ点から取り出した辺の類は、同じcoslice点の元の辺の類。 -/
lemma cosliceTwistedHomMap_vertex_edge_arrow {C : SSet.{u}} {x y : C _⦋0⦌}
    (v : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) _⦋0⦌) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((cosliceTwistedHomMap x y).app (Opposite.op ⦋0⦌) v).val))) =
      Arrow.mk (HomotopyCategory.homMk (cosliceFiberVertexToEdge v)) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change yonedaEquiv ((edgewiseWeightIso 0).inv ≫
    ((cosliceTwistedHomMap x y).app (Opposite.op ⦋0⦌) v).val) =
      yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ v.val.val)
  rw [cosliceTwistedHomMap_app_val, ← Category.assoc, edgewiseWeightIso_zero_inv_comp_cosliceCollapse]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
