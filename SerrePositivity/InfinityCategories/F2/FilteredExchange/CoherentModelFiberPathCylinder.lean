module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentModelFiberPathClass
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseHomotopyFiberCylinder

/-!
概要：元の模型比較の fiber の実際の path 座標が、同じ底固定円柱の fiber 制限となる。
方針：全 path の包含の式と fiberwise path の全円柱の計算を合成する。
規約：全時刻と元の指定類を保持。使われ方：各点の native 錐の可換性への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "a" => smallLeftUnstraighteningProjection F
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "fb" => vertexFiberMap (cf ≫ p) p cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ p) p cg rfl b

/-- 元の模型比較の実際の path の全円柱は、元の同じ底固定円柱の fiber 制限。 -/
lemma coherentCospanConeTotalModelFiberComparison_path_cylinder :
    (β_ (vertexFiber a b) (Δ[1] : SSet.{u})).hom ≫
      uncurry (coherentCospanConeTotalModelFiberComparison F X Y Z C b ≫
        intervalPullbackPath fb gb) =
      (coherentCospanConeFiberPathHomotopy F X Y Z C b).h := by
  apply vertexFiber_hom_ext p b
  rw [Category.assoc, ← uncurry_natural_right]
  have h := (Category.assoc
    (coherentCospanConeTotalModelFiberComparison F X Y Z C b) (intervalPullbackPath fb gb)
    ((ihom (Δ[1] : SSet.{u})).map (vertexFiberι p b))).trans
      (coherentCospanConeTotalModelFiberComparison_path_ι F X Y Z C b)
  have hc := congrArg (fun k => (β_ (vertexFiber a b) (Δ[1] : SSet.{u})).hom ≫ uncurry k) h
  exact hc.trans (fiberwiseHomotopyPoint_fiber_cylinder p a _ _
    (coherentCospanConeRelativePathHomotopy F X Y Z C)
    (coherentCospanConeRelativePathHomotopy_projection F X Y Z C) b)

end SerrePositivity.InfinityCategories.F2
