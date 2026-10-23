module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HomFixedComponent
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalMappingCorePullback
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftFibration

/-!
概要：一次元の同じ全 Hom 作用の同値性を、一成分を固定した実際の fiber 比較で判定する。
方針：同じ底への引き戻しの射影の同値と、left fibration の fiber 判定を使う。
規約：固定成分の比較の同値性は未証明の入力として明示する。
使われ方：一般の Cat∞ 値分類の、一次元セルの Hom 比較の残る入力を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
local notation "s" => (cocartesianHomSourceComponent F G c)
local notation "e" => (coherentHomIntervalComparison
  (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c))
local notation "t" => (cocartesianHomIntervalEvaluation F G c)

attribute [local instance] cocartesianHomIntervalEvaluation_fibration
attribute [local instance] vertexFiber_quasicategory_of_innerFibration

local instance : LeftFibration s := by
  letI := cocartesianIntervalMappingCore_one_fibration F G
  change LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreMap
    (strictDiagramMappingComponent F.val G.val c)))
  infer_instance

local instance : Quasicategory (cocartesianHomComponentSpace F G c) := by
  unfold cocartesianHomComponentSpace
  infer_instance

/-- 一次元の元の全 Hom 作用が同値であることは、同じ固定成分の全 fiber 比較の同値性と同値。 -/
lemma cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_fixedComponent :
    IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G) ↔
      ∀ b : ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
          (cocartesianTransportDiagramValue G c))) _⦋0⦌,
        IsQCatEquivalence (cocartesianHomFixedComponentComparison F G c b) := by
  have hfst := cocartesianHomComponentSpace_fst_isQCatEquivalence F G c
  have hcomp : IsQCatEquivalence (cocartesianHomComponentComparison F G c) ↔
      IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G) := by
    constructor
    · intro h
      have hh := h.comp hfst
      simpa only [cocartesianHomComponentComparison_fst] using hh
    · intro h
      apply hfst.cancel_right
      rw [cocartesianHomComponentComparison_fst]
      exact h
  rw [← hcomp, leftFibration_isQCatEquivalence_iff_fibers s (pullback.snd t e)
    (cocartesianHomComponentComparison F G c) (cocartesianHomComponentComparison_snd F G c)]
  have hi (b) : IsQCatEquivalence ((vertexFiberPullbackIso t e b).hom) :=
    (qCatEquivalenceOfIso (vertexFiberPullbackIso t e b)).isQCatEquivalence
  constructor
  · intro h b
    have hb := (h b).comp (hi b)
    simpa only [cocartesianHomComponentComparison_fiber] using hb
  · intro h b
    apply (hi b).cancel_right
    rw [cocartesianHomComponentComparison_fiber]
    exact h b

end SerrePositivity.InfinityCategories
