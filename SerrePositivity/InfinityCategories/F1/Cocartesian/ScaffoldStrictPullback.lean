module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldSourceLifting
public import SerrePositivity.InfinityCategories.F1.Simplicial.ReplacementSpanComparison

/-!
概要：元の局所 cospan の path を保った厳密比較が、実際の pullback 上に誘導する射。
方針：三成分の同値と両側の一脚の持ち上げ性を、既存の同時 path 置換へ渡す。
規約：補正成分の元の自然性 path は指定正方形のデータに保持する。
使われ方：元の分類 Hom 作用との照合を経た高次元 Segal 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

local notation "S" => cocartesianScaffoldLocalSource n k p q
local notation "T" => cocartesianScaffoldLocalTarget n k p q
local notation "η" => cocartesianScaffoldStrictComparison n k p q

/-- 同じ局所 cospan の厳密な比較による、実際の二つの pullback の間の射。 -/
def cocartesianScaffoldStrictPullbackMap :
    pullback ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  spanPullbackMap _ _ _ _ ((η).app WalkingCospan.one)
    ((η).app WalkingCospan.left) ((η).app WalkingCospan.right)
    ((η).naturality WalkingCospan.Hom.inl).symm ((η).naturality WalkingCospan.Hom.inr).symm

/-- 同じ path を保持した厳密 cospan 比較の pullback 射は、前合成同値。 -/
lemma cocartesianScaffoldStrictPullbackMap_isPrecompositionEquivalence
    (htail : IsQCatEquivalence
      (cocartesianLocalHomComparison (cocartesianScaffoldTailCell n k) p q)) :
    IsPrecompositionEquivalence (cocartesianScaffoldStrictPullbackMap n k p q) := by
  have hq : F1B.KanEquivalenceLifting ((T).map WalkingCospan.Hom.inl) := by
    intro A B j hj he
    exact cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting n k p q j hj he
  have : Fibration ((T).map WalkingCospan.Hom.inl) :=
    fibration_of_kanEquivalenceLifting_of_kanComplex _ hq
  have : TrivialKanFibration (relativeEquivalencePathMapAt ((T).map WalkingCospan.Hom.inl) 0) :=
    HomotopyLimits.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration _ 0
  exact isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting
    ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr)
    ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr)
    ((η).app WalkingCospan.one) ((η).app WalkingCospan.left) ((η).app WalkingCospan.right)
    ((η).naturality WalkingCospan.Hom.inl).symm ((η).naturality WalkingCospan.Hom.inr).symm
    (cocartesianScaffoldStrictComparison_isQCatEquivalence n k p q htail WalkingCospan.one)
    (cocartesianScaffoldStrictComparison_isQCatEquivalence n k p q htail WalkingCospan.left)
    (cocartesianScaffoldStrictComparison_isQCatEquivalence n k p q htail WalkingCospan.right)
    (cocartesianScaffoldLocalSource_first_kanEquivalenceLifting n k p q) hq

instance cocartesianScaffoldStrictPullback_source_kanComplex :
    KanComplex (pullback ((S).map WalkingCospan.Hom.inl)
      ((S).map WalkingCospan.Hom.inr)) := by
  have : Fibration ((S).map WalkingCospan.Hom.inl) :=
    cocartesianScaffoldLocalSource_first_fibration n k p q
  exact kanComplex_pullback_of_fibration ((S).map WalkingCospan.Hom.inl)
    ((S).map WalkingCospan.Hom.inr)

instance cocartesianScaffoldStrictPullback_target_kanComplex :
    KanComplex (pullback ((T).map WalkingCospan.Hom.inl)
      ((T).map WalkingCospan.Hom.inr)) := by
  have : Fibration ((T).map WalkingCospan.Hom.inl) :=
    fibration_of_kanEquivalenceLifting_of_kanComplex _
      (cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting n k p q)
  exact kanComplex_pullback_of_fibration ((T).map WalkingCospan.Hom.inl)
    ((T).map WalkingCospan.Hom.inr)

/-- 同じ実際の厳密 pullback 比較射は、Kan 複体間の同値。 -/
lemma cocartesianScaffoldStrictPullbackMap_isQCatEquivalence
    (htail : IsQCatEquivalence
      (cocartesianLocalHomComparison (cocartesianScaffoldTailCell n k) p q)) :
    IsQCatEquivalence (cocartesianScaffoldStrictPullbackMap n k p q) :=
  (cocartesianScaffoldStrictPullbackMap_isPrecompositionEquivalence n k p q htail).isQCatEquivalence

end SerrePositivity.InfinityCategories
