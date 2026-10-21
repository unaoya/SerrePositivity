module

public import SerrePositivity.InfinityCategories.F1.QCatPostcompositionPullback
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.F1.PullbackFiber

/-!
概要：元の後合成の fiber を、同じ coherent 比較で指定された対角 fiber と比較する。
方針：同じ底への全空間比較の同値を fiber へ制限し、引き戻し fiber の同型を使う。
規約：後合成が left fibration の場合に同じ比較の同値性を証明する。
使われ方：実際の cocartesian 輸送の後合成 fiber の標準比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (A B Z : QCat.{u}) (f : B ⟶ Z)
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom A Z)) _⦋0⦌)
local notation "p" => qCatPostcompositionMap A B Z f
local notation "q" => compositionCorrespondenceDiagonal
  (coherentNerveVertex A) (coherentNerveEdge f)
local notation "e" => coherentHomIntervalComparison A Z

attribute [local instance] compositionCorrespondenceDiagonal_fibration
attribute [local instance] compositionCorrespondence_kanComplex
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance : Quasicategory (qCatPostcompositionPullback A B Z f) := by
  unfold qCatPostcompositionPullback
  infer_instance

/-- 元の後合成の fiber から、同じ全体比較が誘導する指定対角 fiber への比較。 -/
def qCatPostcompositionFiberComparison :
    vertexFiber p b ⟶ vertexFiber q (NatTrans.app e (Opposite.op ⦋0⦌) b) :=
  vertexFiberMap p (pullback.snd q e) (qCatPostcompositionPullbackComparison A B Z f)
    (qCatPostcompositionPullbackComparison_snd A B Z f) b ≫
      (vertexFiberPullbackIso q e b).hom

/-- 同じ fiber 比較の全空間への包含は、元の全体比較を厳密に回収する。 -/
lemma qCatPostcompositionFiberComparison_ι :
    qCatPostcompositionFiberComparison A B Z f b ≫
        vertexFiberι q (NatTrans.app e (Opposite.op ⦋0⦌) b) =
      vertexFiberι p b ≫ coherentCompositionCorrespondence A B Z f := by
  rw [qCatPostcompositionFiberComparison, Category.assoc, vertexFiberPullbackIso_hom_ι,
    ← Category.assoc, vertexFiberMap_ι, Category.assoc,
    qCatPostcompositionPullbackComparison_fst]

/-- 元の後合成が left fibration なら、同じ指定対角 fiber への標準比較は同値。 -/
lemma qCatPostcompositionFiberComparison_isQCatEquivalence [LeftFibration p] :
    IsQCatEquivalence (qCatPostcompositionFiberComparison A B Z f b) := by
  have h := (leftFibration_isQCatEquivalence_iff_fibers p (pullback.snd q e)
    (qCatPostcompositionPullbackComparison A B Z f)
    (qCatPostcompositionPullbackComparison_snd A B Z f)).mp
      (qCatPostcompositionPullbackComparison_isQCatEquivalence A B Z f) b
  exact h.comp (qCatEquivalenceOfIso (vertexFiberPullbackIso q e b)).isQCatEquivalence

end SerrePositivity.InfinityCategories
