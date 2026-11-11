module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramTriangle
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramArrowEndpoints
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramSimplexCurryFaces

/-!
概要：元の豊穣三角形の面は、同じ比較を使う元の区間図式。
方針：三点図式の同じ面を制限し、各成分の恒等・合成を計算する。
規約：全対象と全高次 Hom の図式の等式。
使われ方：比較三角形の curry を元の比較辺へ厳密に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 各対象と各射で同じ元の作用を持つ豊穣図式は等しい。 -/
lemma QuasicategoryEnrichedDiagram.extPointwise
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (ho : ∀ j, D.obj j = E.obj j)
    (hm : ∀ {i j} (f : i ⟶ j), HEq (D.map f) (E.map f)) : D = E := by
  cases D with
  | mk od md idd cd =>
    cases E with
    | mk oe me ide ce =>
      have hobj : od = oe := funext ho
      cases hobj
      have hmap : @md = @me := by
        funext i j f
        exact eq_of_heq (hm f)
      cases hmap
      rfl

/-- 元の三角形の最初の面は、元の最初の比較の同じ区間図式。 -/
lemma quasicategoryEnrichedDiagramTriangle_face_first
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E F : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E) (θ : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison E F) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedDiagramTriangle η θ).reindex
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramSimplexFaceIndex (2 : Fin 3) J) = η.arrowDiagram := by
  apply QuasicategoryEnrichedDiagram.extPointwise
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
