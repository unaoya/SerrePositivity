module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionOuterHorn
public import SerrePositivity.InfinityCategories.F1.Cocartesian.OuterHornHomCriterion

/-!
概要：元の一次元 Hom の同値性を、元の後合成 fiber からの同じ比較射で判定する。
方針：固定成分と後合成 fiber の厳密な同型を、検証済みの外ホーン判定へ接続する。
規約：後合成 fiber からの同じ比較の同値性自体は、まだ未証明の入力。
使われ方：合成三角形全体を使った残りの局所比較の目標を固定する。
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

attribute [local instance] vertexFiber_quasicategory_of_innerFibration
attribute [local instance] cocartesianHomIntervalEvaluation_fibration

local instance : LeftFibration (cocartesianHomSourceComponent F G c) := by
  letI := cocartesianIntervalMappingCore_one_fibration F G
  change LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreMap
    (strictDiagramMappingComponent F.val G.val c)))
  infer_instance

local instance (b : ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
      (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
      (cocartesianIntervalPostcompositionFiber F G b)) := by
  letI := cocartesianIntervalPostcompositionFiber_kanComplex F G b
  infer_instance

/-- 元の固定成分比較の同値性は、元の後合成 fiber からの同じ比較の同値性と同値。 -/
lemma cocartesianHomFixedComponentComparison_isQCatEquivalence_iff_postcomposition
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    IsQCatEquivalence (cocartesianHomFixedComponentComparison F G c b) ↔
      IsQCatEquivalence (cocartesianPostcompositionOuterHornComparison F G b) := by
  rw [cocartesianHomFixedComponentComparison_isQCatEquivalence_iff_outerHorn]
  have hi : IsQCatEquivalence (cocartesianHomSourcePostcompositionFiberIso F G b).hom :=
    (qCatEquivalenceOfIso (cocartesianHomSourcePostcompositionFiberIso F G b)).isQCatEquivalence
  constructor
  · intro h
    apply hi.cancel_left
    rw [cocartesianPostcompositionOuterHornComparison_source]
    exact h
  · intro h
    have hh := hi.comp h
    simpa only [cocartesianPostcompositionOuterHornComparison_source] using hh

/-- 元の全 Hom 作用の同値性は、全後合成 fiber の同じ外ホーン比較の同値性と同値。 -/
lemma cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_postcomposition :
    IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G) ↔
      ∀ b : ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
          (cocartesianTransportDiagramValue G c))) _⦋0⦌,
        IsQCatEquivalence (cocartesianPostcompositionOuterHornComparison F G b) := by
  rw [cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_fixedComponent]
  exact forall_congr' (fun b ↦
    cocartesianHomFixedComponentComparison_isQCatEquivalence_iff_postcomposition F G b)

end SerrePositivity.InfinityCategories
