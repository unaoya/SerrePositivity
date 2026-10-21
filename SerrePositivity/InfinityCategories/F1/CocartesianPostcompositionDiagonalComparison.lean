module

public import SerrePositivity.InfinityCategories.F1.CocartesianPostcompositionDiagonalFiber
public import SerrePositivity.InfinityCategories.F1.CocartesianPostcompositionOuterHorn

/-!
概要：元の後合成 fiber 比較を、同じ合成三角形全体の指定対角 fiber へ移す。
方針：元の外ホーン比較に、検証済みの同じ fiber 同型の逆を続ける。
規約：元の比較射と第二三角形を厳密に回収する。
使われ方：後合成と対角評価の Kan fibration 間の同じ fiber 比較。
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
local notation "d" => cocartesianPostcompositionDiagonalVertex F G b
local notation "p" => compositionCorrespondenceDiagonal (X := CatInfinity) x g

/-- 元の後合成 fiber から同じ指定対角 fiber への、元の作用を保つ比較。 -/
def cocartesianPostcompositionDiagonalComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (cocartesianIntervalPostcompositionFiber F G b) ⟶
      vertexFiber p d :=
  cocartesianPostcompositionOuterHornComparison F G b ≫
    (cocartesianPostcompositionDiagonalFiberIso F G b).inv

/-- 同じ対角 fiber の比較を戻すと、元の外ホーン比較そのものになる。 -/
lemma cocartesianPostcompositionDiagonalComparison_outerHorn :
    cocartesianPostcompositionDiagonalComparison F G b ≫
        (cocartesianPostcompositionDiagonalFiberIso F G b).hom =
      cocartesianPostcompositionOuterHornComparison F G b := by
  rw [cocartesianPostcompositionDiagonalComparison, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 同じ対角 fiber 比較の三角形は、元の固定成分比較の第二三角形そのもの。 -/
lemma cocartesianPostcompositionDiagonalComparison_triangle :
    cocartesianPostcompositionDiagonalComparison F G b ≫ vertexFiberι p d ≫
        pullback.fst ((pre (horn 2 1).ι).app CatInfinity.{u})
          (composableHomHornMap (X := CatInfinity.{u}) x g) =
      (cocartesianHomSourcePostcompositionFiberIso F G b).inv ≫
        cocartesianHomFixedComponentComparison F G (ULift.up 1) b ≫
          cocartesianIntervalSecondTriangleMap F G
            ((coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 1))
              (cocartesianTransportDiagramValue G (ULift.up 1))).app (Opposite.op ⦋0⦌) b) := by
  rw [cocartesianPostcompositionDiagonalComparison, Category.assoc,
    cocartesianPostcompositionDiagonalFiberIso_inv_triangle,
    cocartesianPostcompositionOuterHornComparison_second]

end SerrePositivity.InfinityCategories
