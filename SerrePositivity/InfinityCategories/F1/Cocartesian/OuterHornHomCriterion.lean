module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FixedComponentCompositionFiber
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalHomFiberCriterion

/-!
概要：元の一次元 Hom 作用の同値性を、同じ指定外ホーンへの実際の比較で判定する。
方針：検証済みの外ホーン fiber からの同値を、元の比較の厳密な分解で消去する。
規約：外ホーンへの同じ比較射の同値性自体は、まだ未証明の入力。
使われ方：残る後合成 fiber と外ホーン延長 fiber の同値性の目標を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
local notation "s" => cocartesianHomSourceComponent F G c
local notation "e" => coherentHomIntervalComparison
  (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c)

attribute [local instance] vertexFiber_quasicategory_of_innerFibration
attribute [local instance] cocartesianHomIntervalEvaluation_fibration

local instance : LeftFibration s := by
  letI := cocartesianIntervalMappingCore_one_fibration F G
  change LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreMap
    (strictDiagramMappingComponent F.val G.val c)))
  infer_instance

/-- 元の固定成分比較の同値性は、同じ指定外ホーンへの実際の比較の同値性と同値。 -/
lemma cocartesianHomFixedComponentComparison_isQCatEquivalence_iff_outerHorn
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    IsQCatEquivalence (cocartesianHomFixedComponentComparison F G c b) ↔
      IsQCatEquivalence (cocartesianHomFixedComponentOuterHornComparison F G b) := by
  have he := cocartesianIntervalOuterHornFiberComparison_isQCatEquivalence F G
    (NatTrans.app e (Opposite.op ⦋0⦌) b) (cocartesianIntervalSourceCompositionVertex F G b)
  constructor
  · intro h
    apply he.cancel_right
    rw [cocartesianHomFixedComponentOuterHornComparison_realize]
    exact h
  · intro h
    have hh := h.comp he
    simpa only [cocartesianHomFixedComponentOuterHornComparison_realize] using hh

/-- 元の全 Hom 作用の同値性は、全固定成分での同じ指定外ホーン比較の同値性と同値。 -/
lemma cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_outerHorn :
    IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G) ↔
      ∀ b : ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
          (cocartesianTransportDiagramValue G c))) _⦋0⦌,
        IsQCatEquivalence (cocartesianHomFixedComponentOuterHornComparison F G b) := by
  rw [cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_fixedComponent]
  exact forall_congr' (fun b ↦
    cocartesianHomFixedComponentComparison_isQCatEquivalence_iff_outerHorn F G b)

end SerrePositivity.InfinityCategories
