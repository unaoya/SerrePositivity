module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramTriangleFaces
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparisonLaws

/-!
概要：元の豊穣比較の区間図式は、底の関手による同じ制限と厳密に可換。
方針：二点と底の積上の同じ各成分を比較する。
規約：元の全高次の比較を選び直さない。
使われ方：三角形の最初の辺を既存の底変換比較辺の同じ制限へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 比較の同じ区間図式を作る操作と、底の同じ制限は厳密に可換。 -/
lemma QuasicategoryEnrichedDiagramComparison.arrowDiagram_reindex
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)
    (k : L ⥤ J) :
    (η.reindex k).arrowDiagram = η.arrowDiagram.reindex ((Functor.id (Fin 2)).prod k) := by
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
