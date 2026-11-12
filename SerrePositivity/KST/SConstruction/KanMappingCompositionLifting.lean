module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition
public import SerrePositivity.KST.SConstruction.KanFibrationTriangleLifting

/-! # 元の両辺と全基底合成面を保つ実合成の持ち上げ
概要：fibration に沿い、元の両辺を保持して指定合成辺と全基底三角形を持ち上げる。
方針：既存の内ホーン RLP の実合成面を、同じ合成データへ束ねる。
規約：全基底合成面と実辺の射影を厳密に保持し、源の Kan 性を仮定しない。
使われ方：六対角面消去の上下合成を、同じ全基底像に沿って選ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {E B : SSet.{u}} {x y z : E _⦋0⦌} (a : E.Edge x y) (b : E.Edge y z)
  (p : E ⟶ B)

/-- 元の両辺と、同じ全基底合成辺・全基底合成面を持つ実合成。 -/
structure KanMappingCompositionOver (R : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition (a.map p) (b.map p)) where
  /-- 元の同じ二辺を保持する実合成。 -/
  composition : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition a b
  /-- 合成辺全体の射影を厳密に保持する。 -/
  edge_eq : composition.edge.map p = R.edge
  /-- 全合成面の射影は元の同じ全基底面。 -/
  triangle_projection : SSet.yonedaEquiv.symm composition.triangle.simplex ≫ p =
    SSet.yonedaEquiv.symm R.triangle.simplex

/-- 元の二辺を保ち、指定全基底合成辺と全基底合成面を同時に持ち上げる。 -/
def kanMappingCompositionLiftData [Fibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition (a.map p) (b.map p)) : KanMappingCompositionOver a b p R := by
  apply Classical.choice
  obtain ⟨e, T, hT, he⟩ := exists_kanFibration_liftCompositionTriangle p a b R.edge R.triangle
  refine ⟨⟨⟨e, T⟩, SSet.Edge.ext he, ?_⟩⟩
  exact (SSet.yonedaEquiv_symm_comp _ _).trans (congrArg SSet.yonedaEquiv.symm hT)

end SerrePositivity.KST.SConstruction
