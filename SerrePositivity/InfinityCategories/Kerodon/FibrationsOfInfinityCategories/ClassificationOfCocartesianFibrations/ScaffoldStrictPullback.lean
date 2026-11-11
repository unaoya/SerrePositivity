module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldSourceLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ReplacementSpanComparison

/-!
概要：元の局所 cospan の path を保った厳密比較が、実際の pullback 上に誘導する射。
方針：三成分の同値と両側の一脚の持ち上げ性を、既存の同時 path 置換へ渡す。
規約：補正成分の元の自然性 path は指定正方形のデータに保持する。
使われ方：元の分類 Hom 作用との照合を経た高次元 Segal 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalSource n k p q
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget n k p q
local notation "η" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldStrictComparison n k p q

/-- 同じ局所 cospan の厳密な比較による、実際の二つの pullback の間の射。 -/
def cocartesianScaffoldStrictPullbackMap :
    pullback ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap _ _ _ _ ((η).app WalkingCospan.one)
    ((η).app WalkingCospan.left) ((η).app WalkingCospan.right)
    ((η).naturality WalkingCospan.Hom.inl).symm ((η).naturality WalkingCospan.Hom.inr).symm

/-- 同じ path を保持した厳密 cospan 比較の pullback 射は、前合成同値。 -/
lemma cocartesianScaffoldStrictPullbackMap_isPrecompositionEquivalence
    (htail : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) p q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (cocartesianScaffoldStrictPullbackMap n k p q) := by
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting ((T).map WalkingCospan.Hom.inl) := by
    intro A B j hj he
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting n k p q j hj he
  have : Fibration ((T).map WalkingCospan.Hom.inl) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex _ hq
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt ((T).map WalkingCospan.Hom.inl) 0) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration _ 0
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting
    ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr)
    ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr)
    ((η).app WalkingCospan.one) ((η).app WalkingCospan.left) ((η).app WalkingCospan.right)
    ((η).naturality WalkingCospan.Hom.inl).symm ((η).naturality WalkingCospan.Hom.inr).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldStrictComparison_isQCatEquivalence n k p q htail WalkingCospan.one)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldStrictComparison_isQCatEquivalence n k p q htail WalkingCospan.left)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldStrictComparison_isQCatEquivalence n k p q htail WalkingCospan.right)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalSource_first_kanEquivalenceLifting n k p q) hq

instance cocartesianScaffoldStrictPullback_source_kanComplex :
    KanComplex (pullback ((S).map WalkingCospan.Hom.inl)
      ((S).map WalkingCospan.Hom.inr)) := by
  have : Fibration ((S).map WalkingCospan.Hom.inl) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalSource_first_fibration n k p q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanComplex_pullback_of_fibration ((S).map WalkingCospan.Hom.inl)
    ((S).map WalkingCospan.Hom.inr)

instance cocartesianScaffoldStrictPullback_target_kanComplex :
    KanComplex (pullback ((T).map WalkingCospan.Hom.inl)
      ((T).map WalkingCospan.Hom.inr)) := by
  have : Fibration ((T).map WalkingCospan.Hom.inl) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting n k p q)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanComplex_pullback_of_fibration ((T).map WalkingCospan.Hom.inl)
    ((T).map WalkingCospan.Hom.inr)

/-- 同じ実際の厳密 pullback 比較射は、Kan 複体間の同値。 -/
lemma cocartesianScaffoldStrictPullbackMap_isQCatEquivalence
    (htail : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) p q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianScaffoldStrictPullbackMap n k p q) :=
  (cocartesianScaffoldStrictPullbackMap_isPrecompositionEquivalence n k p q htail).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
