module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramTriangleFaces
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramComparisonLaws

/-!
概要：元の豊穣三角形の後の面と長辺の面を、同じ元の比較の区間図式へ戻す。
方針：同じ各成分で面の制限と比較の合成を計算する。
規約：全対象と元の全高次 Hom の図式の等式。
使われ方：元の比較の合成三角形の全ての面を関手空間へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の三角形の次の面は、元の次の比較の同じ区間図式。 -/
lemma quasicategoryEnrichedDiagramTriangle_face_second
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E F : QuasicategoryEnrichedDiagram C J}
    (η : QuasicategoryEnrichedDiagramComparison D E) (θ : QuasicategoryEnrichedDiagramComparison E F) :
    (quasicategoryEnrichedDiagramTriangle η θ).reindex
      (qCatDiagramSimplexFaceIndex (0 : Fin 3) J) = θ.arrowDiagram := by
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

/-- 元の三角形の長辺の面は、元の合成比較の同じ区間図式。 -/
lemma quasicategoryEnrichedDiagramTriangle_face_long
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E F : QuasicategoryEnrichedDiagram C J}
    (η : QuasicategoryEnrichedDiagramComparison D E) (θ : QuasicategoryEnrichedDiagramComparison E F) :
    (quasicategoryEnrichedDiagramTriangle η θ).reindex
      (qCatDiagramSimplexFaceIndex (1 : Fin 3) J) = (η.trans θ).arrowDiagram := by
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

end SerrePositivity.InfinityCategories
