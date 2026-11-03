module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFiberPathEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoTransport

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
local instance : KanComplex (vertexFiber p b) :=
  vertexFiber_kanComplex_of_leftFibration p b

/-- 元の模型 fiber 比較の指定可換同型は同じ二三角形からの相対指定同型の fiber 像。 -/
lemma coherentCospanConeFiberComparisonPathIso_eq :
    functorIsoOfEq ((intervalPullbackPathIso fb gb).precomp m)
      (coherentCospanConeFiberComparisonPath_left F X Y Z C b)
      (coherentCospanConeFiberComparisonPath_right F X Y Z C b) =
    relativeIsoFiberImage p a
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection])
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection])
      (coherentCospanConeRelativePathIso F X Y Z C) b := by
  apply functorIsoOfEq_of_homotopy_h_eq
    (coherentCospanConeFiberComparisonPathHomotopy F X Y Z C b)
    (coherentCospanConeFiberPathHomotopy F X Y Z C b)
  · rw [functorIso_precomp_hom, intervalPullbackPathIso_hom]
    exact (functorHomotopyPrecomp_hom (intervalPullbackPathHomotopy fb gb) m).symm
  · exact (coherentCospanConeFiberPathHomotopy_hom F X Y Z C b).symm
  · exact coherentCospanConeFiberComparisonPathHomotopy_h F X Y Z C b

end SerrePositivity.InfinityCategories.F2
