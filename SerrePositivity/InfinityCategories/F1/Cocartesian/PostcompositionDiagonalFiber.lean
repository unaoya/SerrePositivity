module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionHornBoundary
public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondenceFiber
public import SerrePositivity.InfinityCategories.F1.VertexFiberPointIso

/-!
概要：元の指定外ホーン fiber を、同じ合成三角形全体の対角 fiber と同定する。
方針：外ホーン pullback の fiber 同型と、検証済みの指定境界の等式を合成する。
規約：元の三角形への実際の射を保持する。
使われ方：元の後合成比較を、Kan fibration 間の fiber 比較として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "x" => coherentNerveVertex (cocartesianTransportDiagramValue F (ULift.up 0))
local notation "g" => cocartesianIntervalCompositionFirstEdge G
local notation "v" => NatTrans.app
  (coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1))) (Opposite.op ⦋0⦌) b
local notation "d" => cocartesianPostcompositionDiagonalVertex F G b
local notation "s₀" => cocartesianIntervalSourceCompositionVertex F G b
local notation "q" => cocartesianIntervalOuterHornMap F G v
local notation "r" => NatTrans.app (pre (SSet.Subcomplex.ι (horn 2 2))) CatInfinity
local notation "p" => compositionCorrespondenceDiagonal (X := CatInfinity) x g

/-- 元の指定外ホーン fiber と、同じ指定対角上の合成三角形 fiber の厳密な同型。 -/
def cocartesianPostcompositionDiagonalFiberIso :
    vertexFiber p d ≅ vertexFiber r (NatTrans.app q (Opposite.op ⦋0⦌) s₀) :=
  compositionCorrespondenceFiberIso (X := CatInfinity.{u}) x g d ≪≫
    vertexFiberPointIso r (cocartesianPostcompositionHornBoundary_vertex F G b)

/-- 同じ fiber 同型は、元の第二三角形への射を保持する。 -/
lemma cocartesianPostcompositionDiagonalFiberIso_hom_ι :
    (cocartesianPostcompositionDiagonalFiberIso F G b).hom ≫
        vertexFiberι r (NatTrans.app q (Opposite.op ⦋0⦌) s₀) =
      vertexFiberι p d ≫
        pullback.fst ((pre (horn 2 1).ι).app CatInfinity.{u})
          (composableHomHornMap (X := CatInfinity.{u}) x g) := by
  rw [cocartesianPostcompositionDiagonalFiberIso, Iso.trans_hom, Category.assoc,
    vertexFiberPointIso_hom_ι, compositionCorrespondenceFiberIso_hom_ι]

/-- 逆の同型で回収する三角形も、同じ元の第二三角形そのもの。 -/
lemma cocartesianPostcompositionDiagonalFiberIso_inv_triangle :
    (cocartesianPostcompositionDiagonalFiberIso F G b).inv ≫ vertexFiberι p d ≫
        pullback.fst ((pre (horn 2 1).ι).app CatInfinity.{u})
          (composableHomHornMap (X := CatInfinity.{u}) x g) =
      vertexFiberι r (NatTrans.app q (Opposite.op ⦋0⦌) s₀) := by
  rw [← cocartesianPostcompositionDiagonalFiberIso_hom_ι, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories
