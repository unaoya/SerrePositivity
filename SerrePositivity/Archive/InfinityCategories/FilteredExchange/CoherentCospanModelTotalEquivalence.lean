module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelFiberEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy

/-!
概要：各点の native 錐の極限性から元の全空間模型比較の同値性を証明する。
方針：fiber 表示の同型を消去し、left fibration の各 fiber による同値判定を使う。
規約：元の底上の比較射を保持。使われ方：coherent filtered 図式の有限極限交換。
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
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "a" => smallLeftUnstraighteningProjection F
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "q" => fiberwiseIntervalPullbackProjection p cf cg
local notation "m" => coherentCospanConeTotalModelComparison F X Y Z C
local notation "hm" => coherentCospanConeTotalModelComparison_over_base F X Y Z C
local instance : LeftFibration (cf ≫ p) := by
  rw [coherentTransformationTotalMap_projection]
  infer_instance
local instance : LeftFibration (cg ≫ p) := by
  rw [coherentTransformationTotalMap_projection]
  infer_instance
local instance : LeftFibration q :=
  fiberwiseIntervalPullbackProjection_leftFibration p cf cg
local instance (b : B _⦋0⦌) : KanComplex (vertexFiber a b) :=
  vertexFiber_kanComplex_of_leftFibration _ _
local instance (b : B _⦋0⦌) : KanComplex (vertexFiber q b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 元の全空間比較の fiber 制限そのものが同値である。 -/
lemma coherentCospanConeTotalFiberMap_isQCatEquivalence (b : B _⦋0⦌)
    (hc : IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsQCatEquivalence (vertexFiberMap a q m hm b) := by
  have h := coherentCospanConeTotalModelFiberComparison_homotopyEquivalence F X Y Z C b hc
  have : KanComplex (intervalPullback
      (vertexFiberMap (cf ≫ p) p cf rfl b) (vertexFiberMap (cg ≫ p) p cg rfl b)) :=
    HomotopyLimits.kanComplex_of_iso (fiberwisePullbackFiberIso p cf cg b)
  exact (qCatEquivalenceOfIso (fiberwisePullbackFiberIso p cf cg b)).isQCatEquivalence
    |>.cancel_right h.isQCatEquivalence

local instance [Quasicategory B] : Quasicategory (fiberwiseIntervalPullback p cf cg) :=
  quasicategory_of_innerFibration q

/-- 全ての点で元の native 錐が極限なら、元の全空間比較が同値である。 -/
lemma coherentCospanConeTotalModelComparison_isQCatEquivalence [Quasicategory B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsQCatEquivalence m := by
  have : Quasicategory (smallLeftUnstraightening F) := quasicategory_of_innerFibration a
  have : Quasicategory (fiberwiseIntervalPullback p cf cg) :=
    quasicategory_of_innerFibration q
  exact isQCatEquivalence_of_leftFibration_fibers a q m hm
    (fun b => coherentCospanConeTotalFiberMap_isQCatEquivalence F X Y Z C b (hc b))

/-- 同じ元の全空間模型比較は弱ホモトピー同値でもある。 -/
lemma coherentCospanConeTotalModelComparison_isWeakHomotopyEquivalence [Quasicategory B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsWeakHomotopyEquivalence m := by
  have h := coherentCospanConeTotalModelComparison_isQCatEquivalence F X Y Z C hc
  exact h.isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
