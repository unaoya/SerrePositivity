module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramTriangleFaces
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparisonLaws

/-!
概要：元の比較の区間図式は、全対象・全 Hom の元の豊穣前合成と厳密に可換。
方針：二点と底の積上の元の対象と射を照合する。
規約：元の比較成分と全高次の作用を保持する。
使われ方：二回目の底変換比較の同じ大域区間族を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の同じ比較の区間図式を作る操作は、豊穣前合成と厳密に可換。 -/
lemma QuasicategoryEnrichedDiagramComparison.arrowDiagram_precompose
    {C : Type v} {L : Type w} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L] {J : Type u} [Category.{u} J]
    {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)
    (R : EnrichedFunctor SSet.{u} L C) :
    (η.precompose R).arrowDiagram = η.arrowDiagram.precompose R := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram.extPointwise
  · rintro ⟨i, a⟩
    fin_cases i <;> rfl
  · intro i j f
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    fin_cases i <;> fin_cases j
    all_goals first
    | have h := leOfHom f.1
      change (1 : ℕ) ≤ 0 at h
      omega
    | apply heq_of_eq
      apply Subtype.ext
      funext X
      rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
