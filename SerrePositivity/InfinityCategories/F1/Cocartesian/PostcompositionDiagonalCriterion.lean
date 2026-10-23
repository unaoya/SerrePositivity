module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionDiagonalComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionHomCriterion

/-!
概要：元の一次元 Hom の同値性を、元の後合成と対角評価の同じ fiber 比較で判定する。
方針：検証済みの外ホーン判定を、同じ対角 fiber との厳密な同型で移す。
規約：同じ fiber 比較の同値性自体は未証明で、分類同値の完了とは主張しない。
使われ方：残る局所比較を二つの Kan fibration の fiber の比較へ接続する。
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
attribute [local instance] compositionCorrespondenceFiber_kanComplex

local instance (b : ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
      (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
      (cocartesianIntervalPostcompositionFiber F G b)) := by
  letI := cocartesianIntervalPostcompositionFiber_kanComplex F G b
  infer_instance

/-- 同じ対角 fiber 比較の同値性は、元の外ホーン比較の同値性と必要十分。 -/
lemma cocartesianPostcompositionDiagonalComparison_isQCatEquivalence_iff
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    IsQCatEquivalence (cocartesianPostcompositionDiagonalComparison F G b) ↔
      IsQCatEquivalence (cocartesianPostcompositionOuterHornComparison F G b) := by
  have hi : IsQCatEquivalence (cocartesianPostcompositionDiagonalFiberIso F G b).hom :=
    (qCatEquivalenceOfIso (cocartesianPostcompositionDiagonalFiberIso F G b)).isQCatEquivalence
  constructor
  · intro h
    have hh := h.comp hi
    simpa only [cocartesianPostcompositionDiagonalComparison_outerHorn] using hh
  · intro h
    apply hi.cancel_right
    rw [cocartesianPostcompositionDiagonalComparison_outerHorn]
    exact h

/-- 元の全 Hom 作用の同値性は、同じ全後合成・対角 fiber 比較の同値性と必要十分。 -/
lemma cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_diagonal :
    IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G) ↔
      ∀ b : ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
          (cocartesianTransportDiagramValue G c))) _⦋0⦌,
        IsQCatEquivalence (cocartesianPostcompositionDiagonalComparison F G b) := by
  rw [cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_postcomposition]
  exact forall_congr' (fun b ↦
    (cocartesianPostcompositionDiagonalComparison_isQCatEquivalence_iff F G b).symm)

end SerrePositivity.InfinityCategories
