module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison

/-!
概要：底全体で自然な豊穣比較の、二点と底の積上の全高次の作用。
方針：二点の両端で元の作用を使い、交差する射は同じ比較の自然性で結ぶ。
規約：元の通常の比較の図式を全パラメーターで保持する。
使われ方：底変換比較の全 fibration にわたる coherent な実現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
  (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)

/-- 比較の二点と底の積の各対象で、元の豊穣関手を使う。 -/
def QuasicategoryEnrichedDiagramComparison.arrowObj
    (_η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E) (i : Fin 2 × J) :
    EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} :=
  Fin.cases (D.obj i.2) (fun _ ↦ E.obj i.2) i.1

/-- 比較の二点と底の積の全射は、元の全高次 Hom に自然な同じ作用を持つ。 -/
def QuasicategoryEnrichedDiagramComparison.arrowMap {i j : Fin 2 × J} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (η.arrowObj i) (η.arrowObj j) := by
  refine ⟨fun X ↦ ?_, ?_⟩
  · rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (η.arrow X).map f
      | succ j => obtain rfl : j = 0 := Subsingleton.elim _ _; exact (η.arrow X).map f
    | succ i =>
      obtain rfl : i = 0 := Subsingleton.elim _ _
      cases j using Fin.cases with
      | zero => exact (η.arrow X).map f
      | succ j => obtain rfl : j = 0 := Subsingleton.elim _ _; exact (η.arrow X).map f
  intro X Y
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  fin_cases i <;> fin_cases j
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, h⟩
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedComparison_app (D.map f.2) X Y h (𝟙 n) x
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, h⟩
    have hE := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedComparison_app (E.map f.2) X Y h (𝟙 n)
      (((η.app a).val X).app n x)
    have hη := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedComparison_app (η.app a) X Y h (𝟙 n) x
    exact hE.trans (congrArg (fun y ↦ ((E.map f.2).val Y).app n y) hη)
  · have hf := leOfHom f.1
    change (1 : Fin 2) ≤ 0 at hf
    omega
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, h⟩
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedComparison_app (E.map f.2) X Y h (𝟙 n) x

/-- 同じ比較を二点と底の積上の一つの豊穣図式へ束ねる。 -/
def QuasicategoryEnrichedDiagramComparison.arrowDiagram :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C (Fin 2 × J) where
  obj := η.arrowObj
  map := η.arrowMap
  map_id i X := by
    rcases i with ⟨i, a⟩
    fin_cases i <;> exact (η.arrow X).map_id _
  map_comp {i j k} f g X := by
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    rcases k with ⟨k, c⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> exact (η.arrow X).map_comp f g

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
