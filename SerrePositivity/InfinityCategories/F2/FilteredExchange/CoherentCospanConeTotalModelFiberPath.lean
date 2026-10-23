module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanConeTotalModelFiber

/-!
概要：全空間比較の各 fiber の全 path 座標を元の指定底固定円柱へ照合する。
方針：元の fiber 同型の path 座標と包含の式に全空間比較の path 式を続ける。
規約：全単体で一致。使われ方：各点の引き戻し錐の指定可換性との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "a" => smallLeftUnstraighteningProjection F
local notation "q" => fiberwiseIntervalPullbackProjection p cf cg
local notation "vf" => vertexFiberMap a q (coherentCospanConeTotalModelComparison F X Y Z C)
  (coherentCospanConeTotalModelComparison_over_base F X Y Z C) b
local notation "fb" => vertexFiberMap (cf ≫ p) p cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ p) p cg rfl b

/-- 概要：各 fiber の全 path を元の全空間へ含めると元の指定 path の制限そのもの。
方針：元の fiber 比較・包含の式と全空間比較の path 式。
規約：全 path 座標の厳密な一致。使われ方：元の各点の可換 path の識別。 -/
lemma coherentCospanConeTotalModelFiberComparison_path_ι :
    coherentCospanConeTotalModelFiberComparison F X Y Z C b ≫ intervalPullbackPath fb gb ≫
      (ihom (Δ[1] : SSet.{u})).map (vertexFiberι p b) =
        vertexFiberι a b ≫ coherentCospanConeTotalModelPath F X Y Z C ≫
          pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) := by
  have h : coherentCospanConeTotalModelFiberComparison F X Y Z C b ≫
      intervalPullbackPath fb gb = vf ≫ fiberwisePullbackFiberPath p cf cg b := by
    change (vf ≫ fiberwisePullbackFiberComparison p cf cg b) ≫ _ = _
    rw [Category.assoc, fiberwisePullbackFiberComparison_path]
  rw [← Category.assoc, h, Category.assoc, fiberwisePullbackFiberPath_ι,
    ← Category.assoc, vertexFiberMap_ι]
  exact congrArg (fun k : smallLeftUnstraightening F ⟶ fiberwiseFunctorSpace p Δ[1] =>
    vertexFiberι a b ≫ k ≫
      pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B))
    (coherentCospanConeTotalModelComparison_path F X Y Z C)

end SerrePositivity.InfinityCategories.F2
