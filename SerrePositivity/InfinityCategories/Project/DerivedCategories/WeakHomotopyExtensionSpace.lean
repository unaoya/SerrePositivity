module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakMappingSpaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-! # 弱同値に沿う Kan 標的への延長の可縮な空間

概要：写像と延長ホモトピーの全高次族を、前合成の path 置換の fiber として作る。
方針：Kan 標的への前合成の同値性を、trivial Kan fibration とその fiber へ移す。
規約：単なるホモトピー類の一意性より強い全境界充填を供給する。
使われ方：屋根の評価と降下の coherent な選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet

/-- 弱同値に沿う延長とその比較の、可逆 path による空間。 -/
def weakHomotopyExtensionSpace {A B Z : SSet.{u}} (w : A ⟶ B) (f : A ⟶ Z) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap ((pre w).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)

/-- 延長の空間から、延長写像そのものの関手空間への射影。 -/
def weakHomotopyExtensionEvaluation {A B Z : SSet.{u}} (w : A ⟶ B) (f : A ⟶ Z) :
    weakHomotopyExtensionSpace w f ⟶ (ihom B).obj Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap ((pre w).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection ((pre w).app Z)

/-- 弱同値に沿う Kan 標的への延長空間は、全境界を充填する可縮 Kan 複体。 -/
theorem weakHomotopyExtensionSpace_isContractibleKan {A B Z : SSet.{u}} [KanComplex Z]
    {w : A ⟶ B} (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence w) (f : A ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (weakHomotopyExtensionSpace w f) := by
  have := (hw.precompose_kan Z).isQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 空間全体で動く延長は、元の写像と coherent な比較を持つ。 -/
def weakHomotopyExtensionEvaluationIso {A B Z : SSet.{u}} [KanComplex Z]
    (w : A ⟶ B) (f : A ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakHomotopyExtensionEvaluation w f ≫ (pre w).app Z)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementFunctorIso ((pre w).app Z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap ((pre w).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
  simpa only [weakHomotopyExtensionEvaluation, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
