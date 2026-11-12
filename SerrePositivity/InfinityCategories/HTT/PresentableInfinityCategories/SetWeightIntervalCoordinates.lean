module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightElementsInterval
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramOrdinaryEdgeSimplex

/-!
概要：要素の圏の区間族から元の添字へ戻すと、元の係数の区間図式を得る。
方針：区間の二頂点と三種類の射で、同じ元の射を計算する。
規約：要素のラベルを保つ自然変換を使い、その後にだけ射影する。
使われ方：G8 の pointed 区間族の底を、元の重みの辺の全 prism と同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 元の要素の区間族の係数は、同じ重みの通常の自然変換の係数図式である。 -/
lemma setWeightElementsInterval_coefficients {I : Type u} [SmallCategory I]
    {X Y : I ⥤ Type u} (φ : X ⟶ Y) :
    Functor.uncurry.obj (ComposableArrows.mk₁ (setWeightElementsIntervalTransformation φ)) ⋙
      Functor.Elements.π (setWeightIntervalDiagram φ) ⋙ setWeightIntervalDiagram φ ⋙ setsToKan =
    (𝟭 (Fin 2)).prod (Functor.Elements.π X) ⋙
      Functor.uncurry.obj (ComposableArrows.mk₁
        (kanDiagramUnderlyingTransformation (F := ⟨X ⋙ setsToKan, trivial⟩)
          (G := ⟨Y ⋙ setsToKan, trivial⟩) (SetWeight.coefficientsMap φ))) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    rintro ⟨a, e⟩
    fin_cases a <;> rfl
  case h_map =>
    rintro ⟨a, e⟩ ⟨b, f⟩ g
    fin_cases a <;> fin_cases b
    all_goals first
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) (leOfHom g.1))
    | simp [setWeightElementsIntervalTransformation, setWeightElementsIntervalZero,
        setWeightElementsIntervalOne, setWeightIntervalDiagram,
        kanDiagramUnderlyingTransformation, SetWeight.coefficientsMap, Functor.uncurry]
    all_goals rfl

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
