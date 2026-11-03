module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.Compact.CoconeFiberPrism

/-!
概要：元の余錐の実際の fiber 写像を、同じ全余錐の unstraightening 内の prism に戻す。
方針：元の pointed prism と元の join 円柱を同じ引き戻しへ持ち上げる。
規約：始点は元の図式部分の包含、終点は元の fiber 写像と指定頂点の包含の合成。
使われ方：一つの全空間表現で prism 全体を送り、宇宙変更後の同じ終点を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の全余錐を右包含の頂点で評価すると、同じ元の指定頂点となる。 -/
lemma coconeFiberVertex_value (c : JoinCocone F) :
    c.val.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u + 1}))) =
      c.vertex := by
  rw [JoinCocone.vertex_eq, SSet.yonedaEquiv_comp]

/-- 元の指定頂点の pointed fiber を、同じ全余錐の実際の全空間へ含める。 -/
def coconeFiberVertexInclusion (c : JoinCocone F) :
    vertexFiber pointedSpaceProjection c.vertex ⟶ leftUnstraightening c.val :=
  pullback.lift (vertexFiberι pointedSpaceProjection c.vertex)
    (SSet.const (SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u + 1})))) (by
      rw [vertexFiberι_comp, SSet.const_comp, coconeFiberVertex_value])

/-- 指定頂点の包含は、元の pointed fiber の包含そのものを回収する。 -/
lemma coconeFiberVertexInclusion_pointed (c : JoinCocone F) :
    coconeFiberVertexInclusion c ≫ pullback.fst pointedSpaceProjection c.val =
      vertexFiberι pointedSpaceProjection c.vertex := pullback.lift_fst _ _ _

/-- 指定頂点の包含の底は、元の右包含の頂点に厳密に定値。 -/
lemma coconeFiberVertexInclusion_projection (c : JoinCocone F) :
    coconeFiberVertexInclusion c ≫ leftUnstraighteningProjection c.val =
      SSet.const (SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u + 1}))) :=
  pullback.lift_snd _ _ _

/-- 元の指定 fiber 写像の prism を、同じ全余錐自身の元の全空間へ戻す。 -/
def coconeFiberTotalPrism (c : JoinCocone F) :
    (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ leftUnstraightening c.val :=
  pullback.lift (coconeFiberPrism c) (coconeFiberBasePrism (F := F))
    (coconeFiberPrism_projection c)

/-- 同じ全空間 prism の pointed 成分は、元の指定 fiber 写像の prism そのもの。 -/
lemma coconeFiberTotalPrism_pointed (c : JoinCocone F) :
    coconeFiberTotalPrism c ≫ pullback.fst pointedSpaceProjection c.val =
      coconeFiberPrism c := pullback.lift_fst _ _ _

/-- 同じ全空間 prism の底も、元の join 円柱そのもの。 -/
lemma coconeFiberTotalPrism_projection (c : JoinCocone F) :
    coconeFiberTotalPrism c ≫ leftUnstraighteningProjection c.val =
      coconeFiberBasePrism (F := F) := pullback.lift_snd _ _ _


/-- 同じ全空間 prism の始点は、元の図式部分の実際の全空間の包含。 -/
lemma coconeFiberTotalPrism_zero (c : JoinCocone F) :
    prismEndpoint 0 _ ≫ coconeFiberTotalPrism c =
      leftUnstraighteningMap F c.val (joinInl B Δ[0]) c.property := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coconeFiberTotalPrism_pointed,
      coconeFiberPrism_zero, leftUnstraighteningMap_pointed]
  · change (prismEndpoint 0 _ ≫ coconeFiberTotalPrism c) ≫
      leftUnstraighteningProjection c.val =
      leftUnstraighteningMap F c.val (joinInl B Δ[0]) c.property ≫
        leftUnstraighteningProjection c.val
    simp only [Category.assoc, coconeFiberTotalPrism_projection,
      coconeFiberBasePrism_zero, leftUnstraighteningMap_projection]

/-- 同じ全空間 prism の終点は、元の fiber 写像自身と元の指定頂点の包含の合成。 -/
lemma coconeFiberTotalPrism_one (c : JoinCocone F) :
    prismEndpoint 1 _ ≫ coconeFiberTotalPrism c =
      coconeFiberMap c ≫ coconeFiberVertexInclusion c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coconeFiberTotalPrism_pointed,
      coconeFiberPrism_one, coconeFiberVertexInclusion_pointed]
  · change (prismEndpoint 1 _ ≫ coconeFiberTotalPrism c) ≫
      leftUnstraighteningProjection c.val =
      (coconeFiberMap c ≫ coconeFiberVertexInclusion c) ≫ leftUnstraighteningProjection c.val
    simp only [Category.assoc, coconeFiberTotalPrism_projection, coconeFiberBasePrism_one,
      coconeFiberVertexInclusion_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2.Compact
