module
public import SerrePositivity.KST.Fibration.WeakUniversalOre
public import SerrePositivity.KST.LocalizingInvariants.PullbackDiagramFamilies

/-! # 元の W 辺 cospan と普遍 Ore 四角形の全高次図式圏 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)

/-- cospan の指定した上辺が元の W 辺であるという頂点条件。 -/
def IsWeakDenominatorCospan
    (v : ((ihom (horn 2 2 : SSet.{u})).obj B.obj) _⦋0⦌) : Prop :=
  yonedaEquiv (horn₂₂.ι₁₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ B.obj).symm v) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i

/-- W cospan の全関手部分圏。 -/
def weakDenominatorCospans : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsWeakDenominatorCospan i) : SSet.{u})

instance weakDenominatorCospans_quasicategory : Quasicategory (weakDenominatorCospans i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 元の全 cospan 圏への包含。 -/
def weakDenominatorCospanInclusion :
    weakDenominatorCospans i ⟶ (ihom (horn 2 2 : SSet.{u})).obj B.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsWeakDenominatorCospan i)).ι

/-- 元の W cospan に対する、全普遍 pullback の厳密な基底変更。 -/
def weakOreDiagrams : SSet.{u} :=
  pullback (pullbackProjection B.obj) (weakDenominatorCospanInclusion i)

/-- 同じ元の cospan を回収する射影。 -/
def weakOreProjection : weakOreDiagrams i ⟶ weakDenominatorCospans i := pullback.snd _ _

instance weakOreProjection_trivialKanFibration : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (weakOreProjection i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

instance weakOreDiagrams_quasicategory : Quasicategory (weakOreDiagrams i) :=
  quasicategory_of_innerFibration (weakOreProjection i)

end SerrePositivity.KST.Fibration
