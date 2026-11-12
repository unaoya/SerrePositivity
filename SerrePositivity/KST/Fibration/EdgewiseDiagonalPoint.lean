module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints

/-! # 元の点を両端で保持する edgewise の同じ退化辺 -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の頂点の退化辺を、同じ edgewise 解像の頂点とする。 -/
def edgewiseDiagonalPoint (K : SSet.{u}) (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K) _⦋0⦌ := SSet.const v

/-- 同じ退化辺の右端は元の点そのもの。 -/
theorem edgewiseDiagonalPoint_right (K : SSet.{u}) (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K).app (Opposite.op ⦋0⦌) (edgewiseDiagonalPoint K v) = v := by
  change SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}).op (Δ[0] : SSet.{u}) ≫ SSet.const v) = v
  rw [SSet.comp_const, SSet.yonedaEquiv_const]

/-- 同じ退化辺の左端は反転した空間の同じ元の点。 -/
theorem edgewiseDiagonalPoint_left (K : SSet.{u}) (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft K).app (Opposite.op ⦋0⦌) (edgewiseDiagonalPoint K v) =
      SSet.opObjEquiv.symm v := by
  apply SSet.opObjEquiv.injective
  rw [Equiv.apply_symm_apply]
  change SSet.yonedaEquiv ((stdSimplex.opIso ⦋0⦌).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}).op (Δ[0] : SSet.{u}) ≫ SSet.const v) = v
  rw [SSet.comp_const, SSet.comp_const, SSet.yonedaEquiv_const]

end SerrePositivity.KST.Fibration
