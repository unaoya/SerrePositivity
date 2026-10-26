module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLabelBaseline
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionTriangle
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionSquareEvaluation

/-!
概要：三対象ラベルの基準を、既存の全族の合成三角形に照合する。
方針：同じ二重切断の座標を評価する。
規約：二つの Hom の元の単体と全ての面・退化を保つ。
使われ方：基準二胞体の全次数での自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleLabelBaseline_realization
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (l : Fin (n + 1) →o Fin 3) :
    (coherentCompositionTriangle X Y Z).app (Opposite.op ⦋n⦌)
      (stdSimplex.objEquiv.symm (SimplexCategory.mkHom l), (ULift.up σ, ULift.up τ)) =
        triangleLabelBaseline σ τ l := by
  let w := (squareTriangle (0 : Fin 2)).app (Opposite.op ⦋n⦌)
    (stdSimplex.objEquiv.symm (SimplexCategory.mkHom l))
  change (coherentCompositionSquare X Y Z).app (Opposite.op ⦋n⦌)
    (w.1, (w.2, (ULift.up σ, ULift.up τ))) = _
  rw [coherentCompositionSquare_evaluate_cut]
  change coherentCompositionNestedCutSimplex σ τ
    (stdSimplex.objEquiv w.1).toOrderHom (stdSimplex.objEquiv w.2).toOrderHom = _
  have h₁ : (stdSimplex.objEquiv w.1).toOrderHom = triangleUpperLabel l := by
    apply OrderHom.ext
    funext i
    change (squareTriangleSimplex.{max u v} 0).val.1 (l i) =
      (if l i = 2 then (1 : Fin 2) else 0)
    have cases : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    rcases cases (l i) with h | h | h <;> rw [h] <;> decide
  have h₂ : (stdSimplex.objEquiv w.2).toOrderHom = triangleZeroLabel l := by
    apply OrderHom.ext
    funext i
    change (squareTriangleSimplex.{max u v} 0).val.2 (l i) =
      (if l i = 0 then (0 : Fin 2) else 1)
    have cases : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    rcases cases (l i) with h | h | h <;> rw [h] <;> decide
  rw [h₁, h₂]
  rfl

/-- 同じ基準単体は、二短辺の面・退化と三対象ラベルの引き戻しを同時に保つ。 -/
lemma triangleLabelBaseline_naturality
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (l : Fin (n + 1) →o Fin 3) :
    (SimplicialNerve C).map α.op (triangleLabelBaseline σ τ l) =
      triangleLabelBaseline ((SimplicialCategory.sHom X Y).map α.op σ)
        ((SimplicialCategory.sHom Y Z).map α.op τ) (l.comp α.toOrderHom) := by
  let a : ((Δ[2] : SSet.{max u v}) ⊗
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))) _⦋n⦌ :=
    (stdSimplex.objEquiv.symm (SimplexCategory.mkHom l), (ULift.up σ, ULift.up τ))
  have hn := ConcreteCategory.congr_hom
    ((coherentCompositionTriangle X Y Z).naturality α.op) a
  exact (congrArg ((SimplicialNerve C).map α.op)
      (triangleLabelBaseline_realization σ τ l)).symm.trans
    (hn.symm.trans (triangleLabelBaseline_realization
      ((SimplicialCategory.sHom X Y).map α.op σ)
      ((SimplicialCategory.sHom Y Z).map α.op τ) (l.comp α.toOrderHom)))

end SerrePositivity.InfinityCategories
