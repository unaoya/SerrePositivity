module

public import SerrePositivity.InfinityCategories.F2.CoherentModelFiberPathCylinder
public import SerrePositivity.InfinityCategories.F2.IntervalPathPrecompCylinder

/-!
概要：実際の模型 fiber 比較の可換円柱を元の fiber 円柱と両端で照合する。
方針：元の二射影の式と fiber 射の合成則、全 path 円柱の一致を使う。
規約：両端の元の射と全時刻を保持。使われ方：指定可換同型の最終照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "a" => smallLeftUnstraighteningProjection F
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "fb" => vertexFiberMap (cf ≫ p) p cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ p) p cg rfl b
local notation "m" => coherentCospanConeTotalModelFiberComparison F X Y Z C b

/-- 実際の模型比較の指定 path 円柱をそのまま始域に制限する。 -/
def coherentCospanConeFiberComparisonPathHomotopy :=
  functorHomotopyPrecomp (intervalPullbackPathHomotopy fb gb) m

/-- 元の模型の第一合成脚は元の第一全空間合成の fiber 射。 -/
lemma coherentCospanConeFiberComparisonPath_left :
    m ≫ (intervalPullbackLeft fb gb ≫ fb) =
      vertexFiberMap a p (cl ≫ cf) (by
        rw [Category.assoc, coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection]) b := by
  rw [← Category.assoc, coherentCospanConeTotalModelFiberComparison_left]
  exact vertexFiberMap_comp a (cf ≫ p) p cl cf _ rfl b

/-- 元の模型の第二合成脚は元の第二全空間合成の fiber 射。 -/
lemma coherentCospanConeFiberComparisonPath_right :
    m ≫ (intervalPullbackRight fb gb ≫ gb) =
      vertexFiberMap a p (cr ≫ cg) (by
        rw [Category.assoc, coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection]) b := by
  rw [← Category.assoc, coherentCospanConeTotalModelFiberComparison_right]
  exact vertexFiberMap_comp a (cg ≫ p) p cr cg _ rfl b

/-- 実際の模型の可換円柱は元の底固定円柱の fiber 制限と全時刻で一致する。 -/
lemma coherentCospanConeFiberComparisonPathHomotopy_h :
    (coherentCospanConeFiberComparisonPathHomotopy F X Y Z C b).h =
      (coherentCospanConeFiberPathHomotopy F X Y Z C b).h := by
  exact (intervalPullbackPathHomotopy_precomp_cylinder fb gb m).trans
    (coherentCospanConeTotalModelFiberComparison_path_cylinder F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
