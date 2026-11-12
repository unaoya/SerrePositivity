module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightElementsInterval
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightPointedCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Prism

/-!
概要：元の要素の圏の pointed 比較を、重みの射に沿う区間族へまとめる。
方針：区間上の要素の圏の実 prism に、元の pointed 比較を後合成する。
規約：両端は元の比較の pointed 成分であり、別の同値を選ばない。
使われ方：G8 の四角形①で、相対延長の選択独立性へ渡す実際の族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}

/-- 元の重みの射に沿って、元の pointed 比較を全単体で結ぶ区間族。 -/
def setWeightPointedInterval (φ : X ⟶ Y) :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve X.Elements) ⟶
      PointedSpaceInfinity.{u} :=
  uliftSimplexPrism (setWeightElementsIntervalPrism φ) ≫
    setWeightElementsPointed (setWeightIntervalDiagram φ)

/-- 始点包含で制限した区間上の比較は、元の始域の比較そのものである。 -/
lemma setWeightElementsPointed_intervalZero (φ : X ⟶ Y) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (setWeightElementsIntervalZero φ)) ≫
      setWeightElementsPointed (setWeightIntervalDiagram φ) = setWeightElementsPointed X := by
  rw [setWeightElementsPointed_formula, setWeightElementsPointed_formula]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 終点包含で制限した区間上の比較は、元の終域の比較そのものである。 -/
lemma setWeightElementsPointed_intervalOne (φ : X ⟶ Y) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (setWeightElementsIntervalOne φ)) ≫
      setWeightElementsPointed (setWeightIntervalDiagram φ) = setWeightElementsPointed Y := by
  rw [setWeightElementsPointed_formula, setWeightElementsPointed_formula]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- pointed 区間族の始点は元の要素の圏の比較である。 -/
lemma setWeightPointedInterval_zero (φ : X ⟶ Y) :
    simplexPrismVertex 1 0 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve X.Elements)) ≫
      setWeightPointedInterval φ = setWeightElementsPointed X := by
  rw [setWeightPointedInterval, ← Category.assoc, uliftSimplexPrism_vertex]
  change (SSet.uliftFunctor.{u + 1, u}).map (prismEndpoint 0 (nerve X.Elements) ≫ setWeightElementsIntervalPrism φ) ≫ _ = _
  rw [setWeightElementsIntervalPrism_zero, setWeightElementsPointed_intervalZero]

/-- pointed 区間族の終点は元の mapElements で制限した終域の比較である。 -/
lemma setWeightPointedInterval_one (φ : X ⟶ Y) :
    simplexPrismVertex 1 1 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve X.Elements)) ≫
      setWeightPointedInterval φ =
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫ setWeightElementsPointed Y := by
  rw [setWeightPointedInterval, ← Category.assoc, uliftSimplexPrism_vertex]
  change (SSet.uliftFunctor.{u + 1, u}).map (prismEndpoint 1 (nerve X.Elements) ≫ setWeightElementsIntervalPrism φ) ≫ _ = _
  rw [setWeightElementsIntervalPrism_one]
  change (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap φ.mapElements ≫ nerveMap (setWeightElementsIntervalOne φ)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, setWeightElementsPointed_intervalOne]

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
