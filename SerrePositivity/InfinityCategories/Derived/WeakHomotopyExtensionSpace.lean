module
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakMappingSpaces
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Core.VertexFiber

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet

/-- 弱同値に沿う延長とその比較の、可逆 path による空間。 -/
def weakHomotopyExtensionSpace {A B Z : SSet.{u}} (w : A ⟶ B) (f : A ⟶ Z) : SSet.{u} :=
  vertexFiber (equivalencePathReplacementMap ((pre w).app Z)) (functorVertex f)

/-- 延長の空間から、延長写像そのものの関手空間への射影。 -/
def weakHomotopyExtensionEvaluation {A B Z : SSet.{u}} (w : A ⟶ B) (f : A ⟶ Z) :
    weakHomotopyExtensionSpace w f ⟶ (ihom B).obj Z :=
  vertexFiberι (equivalencePathReplacementMap ((pre w).app Z)) (functorVertex f) ≫
    equivalencePathReplacementProjection ((pre w).app Z)

/-- 弱同値に沿う Kan 標的への延長空間は、全境界を充填する可縮 Kan 複体。 -/
theorem weakHomotopyExtensionSpace_isContractibleKan {A B Z : SSet.{u}} [KanComplex Z]
    {w : A ⟶ B} (hw : IsWeakHomotopyEquivalence w) (f : A ⟶ Z) :
    IsContractibleKan (weakHomotopyExtensionSpace w f) := by
  have := (hw.precompose_kan Z).isQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration
  exact vertexFiber_isContractibleKan _ _

/-- 空間全体で動く延長は、元の写像と coherent な比較を持つ。 -/
def weakHomotopyExtensionEvaluationIso {A B Z : SSet.{u}} [KanComplex Z]
    (w : A ⟶ B) (f : A ⟶ Z) :
    FunctorIso (weakHomotopyExtensionEvaluation w f ≫ (pre w).app Z)
      (SSet.const (functorVertex f)) := by
  have h := FunctorIso.precomp (equivalencePathReplacementFunctorIso ((pre w).app Z))
    (vertexFiberι (equivalencePathReplacementMap ((pre w).app Z)) (functorVertex f))
  simpa only [weakHomotopyExtensionEvaluation, Category.assoc, vertexFiberι_comp] using h

end SerrePositivity.InfinityCategories
