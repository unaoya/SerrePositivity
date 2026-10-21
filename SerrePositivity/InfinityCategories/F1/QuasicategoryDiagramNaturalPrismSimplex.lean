module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramDiagonalArrow
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramDiagonalOrder
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramRealization

/-!
概要：同じ自然変換の辺の全パラメーターでの対角実現は、元の prism の同じ単体。
方針：同じ二点図式の通常の対角関手と、その coherent 表示を使う。
規約：底と区間の全次数の単体を同時に保持する。
使われ方：結合同型の分類像と既存の結合区間族を厳密に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 自然変換の同じ辺を任意の区間の射列で引き戻して実現すると、元の prism の単体になる。 -/
lemma quasicategoryDiagramDiagonalSimplex_naturalPrism
    {C : Type u} [Category.{u} C] {F G : QuasicategoryDiagramCategory C}
    (η : F.val ⋙ quasicategoryObjectForget ⟶ G.val ⋙ quasicategoryObjectForget)
    {n : ℕ} (σ : (nerve C) _⦋n⦌) (τ : Fin (n + 1) ⥤ Fin 2) :
    quasicategoryDiagramDiagonalSimplex σ
      ((nerveToCoherent (QuasicategoryDiagramCategory C)).app (Opposite.op ⦋n⦌)
        (τ ⋙ ComposableArrows.mk₁ (quasicategoryDiagramHom η))) =
    (qCatDiagramCoherentNerve
      (qCatDiagramArrow (quasicategoryDiagramQCatTransformation η))).app (Opposite.op ⦋n⦌)
        (ULift.up (τ.prod' σ)) := by
  let B : ULift.{u} (Fin (n + 1)) ⥤ Fin 2 × C :=
    (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙
      τ.prod' σ
  change diagonalQuasicategoryDiagramEvaluation (B ⋙ CategoryTheory.Prod.snd (Fin 2) C)
      (enrichedFunctorOfOrderDiagram (B ⋙ CategoryTheory.Prod.fst (Fin 2) C ⋙
        ComposableArrows.mk₁ (quasicategoryDiagramHom η))) =
    enrichedFunctorOfOrderDiagram
      (B ⋙ qCatDiagramArrow (quasicategoryDiagramQCatTransformation η))
  rw [diagonalQuasicategoryDiagramEvaluation_order,
    quasicategoryDiagramDiagonalFunctor_precomp, quasicategoryDiagramDiagonalFunctor_arrow]

end SerrePositivity.InfinityCategories
