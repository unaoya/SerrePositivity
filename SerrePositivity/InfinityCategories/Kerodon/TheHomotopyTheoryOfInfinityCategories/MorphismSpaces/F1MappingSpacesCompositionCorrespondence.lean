module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ComposableHomHorn
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：第二辺を固定し第一辺を全 Hom 空間で動かす、合成三角形全体の空間。
方針：内ホーン制限を普遍の第一辺・指定第二辺へ引き戻す。
規約：三角形と合成辺は選ばず、その全体を保持する。
使われ方：元の後合成 fiber と指定外ホーン fiber の同値性を全空間の比較で証明する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)

/-- 第一辺を全 Hom 空間で動かし、第二辺を指定辺に固定した全合成三角形の空間。 -/
def compositionCorrespondence : SSet.{u} :=
  pullback ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g)

/-- 同じ全合成三角形から、その元の第一辺への射影。 -/
def compositionCorrespondenceFirst : compositionCorrespondence x g ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  pullback.snd _ _

/-- 同じ全合成三角形の元の三角形への普遍評価。 -/
def compositionCorrespondenceEvaluation : (Δ[2] : SSet.{u}) ⊗ compositionCorrespondence x g ⟶ X :=
  uncurry (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g))

/-- 第一辺への同じ射影は、内ホーン制限の自明 Kan 性から trivial Kan fibration。 -/
lemma compositionCorrespondenceFirst_trivialKanFibration [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (compositionCorrespondenceFirst x g) := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (horn 2 1).ι).app X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _
      (innerAnodyneExtensions.horn_ι (by decide) (by decide)) X
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

/-- 合成三角形全体の空間は、第一辺の Kan 空間上の自明 Kan fibration により Kan。 -/
lemma compositionCorrespondence_kanComplex [Quasicategory X] :
    KanComplex (compositionCorrespondence x g) := by
  letI := compositionCorrespondenceFirst_trivialKanFibration x g
  letI : Fibration (compositionCorrespondenceFirst x g) :=
    (SSet.modelCategoryQuillen.fibration_iff _).2 (by
      intro A B i hi
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := compositionCorrespondenceFirst x g) i
        (J_le_monomorphisms i hi))
  exact isFibrant_of_fibration (compositionCorrespondenceFirst x g)

attribute [local instance] compositionCorrespondence_kanComplex

/-- 同じ全合成三角形から第一辺への射影は、元の Hom 空間の同値。 -/
lemma compositionCorrespondenceFirst_isQCatEquivalence [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (compositionCorrespondenceFirst x g) := by
  letI := compositionCorrespondenceFirst_trivialKanFibration x g
  letI := compositionCorrespondence_kanComplex x g
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

/-- 同じ普遍三角形の内ホーン制限は、元の第一辺の普遍族と指定第二辺のホーン。 -/
lemma compositionCorrespondenceEvaluation_horn :
    ((horn 2 1).ι ▷ compositionCorrespondence x g) ≫ compositionCorrespondenceEvaluation x g =
      uncurry (compositionCorrespondenceFirst x g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) := by
  unfold compositionCorrespondenceEvaluation compositionCorrespondenceFirst
  rw [← uncurry_pre_app, pullback.condition]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
