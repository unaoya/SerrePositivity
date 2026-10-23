module

public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionSquareEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionDiagonalSimplex
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionCorrespondence

/-!
概要：coherent 合成の同じ対角作用は、元の豊穣合成の標準 Hom 比較そのもの。
方針：全単体の切断図式の等式を四角形の対角と三角形の対角へ戻す。
規約：元の合成族と全体比較を変更しない。
使われ方：後合成と対角評価の厳密な可換四角形を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 標準正方形の対角は、同じ時刻を二つの座標へ送る。 -/
lemma squareDiagonal_eq_lift : squareDiagonal.{u} = lift (𝟙 Δ[1]) (𝟙 Δ[1]) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C)

/-- 同じ coherent 合成四角形の対角は、元の豊穣合成の標準区間族そのもの。 -/
lemma coherentCompositionSquare_diagonal :
    (squareDiagonal ▷ _) ≫ (α_ (Δ[1] : SSet.{max u v}) Δ[1] _).hom ≫
      coherentCompositionSquare X Y Z =
    intervalMappingUncurry (coherentHomComposition X Y Z ≫ coherentHomIntervalComparison X Z) := by
  rw [squareDiagonal_eq_lift, intervalMappingUncurry_precomp]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨⟨σ⟩, ⟨τ⟩⟩⟩
  change (coherentCompositionSquare X Y Z).app (Opposite.op ⦋n⦌)
    (t, (t, (ULift.up σ, ULift.up τ))) =
      (intervalMappingUncurry (coherentHomIntervalComparison X Z)).app
        (Opposite.op ⦋n⦌)
        (t, ULift.up ((eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)))
  rw [coherentCompositionSquare_evaluate_diagonal, coherentCompositionDiagonalCutSimplex_eq,
    coherentHomIntervalComparison_evaluate_cut]

/-- 同じ合成三角形の対角は、元の豊穣合成の標準区間族そのもの。 -/
lemma coherentCompositionTriangle_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ coherentCompositionTriangle X Y Z =
      intervalMappingUncurry (coherentHomComposition X Y Z ≫ coherentHomIntervalComparison X Z) := by
  rw [coherentCompositionTriangle, squarePrismTriangle_diagonal,
    coherentCompositionSquare_diagonal]

/-- 第二射を固定した同じ全体比較は、対角評価で元の豊穣合成と厳密に可換。 -/
lemma coherentCompositionCorrespondence_diagonal (f : Y ⟶ Z) :
    coherentCompositionCorrespondence X Y Z f ≫
      compositionCorrespondenceDiagonal (coherentNerveVertex X) (coherentNerveEdge f) =
    coherentCompositionFixedParameter X Y Z f ≫ coherentHomComposition X Y Z ≫
      coherentHomIntervalComparison X Z := by
  apply intervalMappingUncurry_injective
  rw [coherentCompositionCorrespondence_diagonal_uncurry, coherentCompositionFixedTriangle,
    ← Category.assoc, ← whisker_exchange, Category.assoc,
    coherentCompositionTriangle_diagonal, ← intervalMappingUncurry_precomp]

end SerrePositivity.InfinityCategories
