module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleSimplex
public import SerrePositivity.InfinityCategories.F1.CoherentCompositionFixedTriangle
public import SerrePositivity.InfinityCategories.F1.CoherentCompositionSquareEvaluation

/-!
概要：第二三角形の標準切断図式は、同じ coherent 合成三角形の族の評価そのもの。
方針：標準正方形の零番三角形の二つの時間座標と、四角形の評価式を使う。
規約：元の零成分の全単体と同じ終域輸送を保持する。
使われ方：第二三角形の単体ごとの一致を族の等式へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ標準第二三角形の切断図式は、元の零成分の合成三角形を評価した値。 -/
lemma cocartesianSecondTriangleCanonicalSimplex_eq_evaluation
    (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌) :
    cocartesianSecondTriangleCanonicalSimplex F G a s =
      (coherentCompositionFixedTriangle
        (cocartesianTransportDiagramValue F (ULift.up 0))
        (cocartesianTransportDiagramValue G (ULift.up 0))
        (cocartesianTransportDiagramValue G (ULift.up 1))
        (show cocartesianTransportDiagramValue G (ULift.up 0) ⟶
          cocartesianTransportDiagramValue G (ULift.up 1) from G.val.map strictIntervalIndexArrow)).app
        (Opposite.op ⦋n⦌) (a, ULift.up
          ((quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))).app
            (Opposite.op ⦋n⦌) s)) := by
  have ht := congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌) a) (squareTriangle_zero_time.{u + 1})
  have hb := congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌) a) (squareTriangle_zero_base.{u + 1})
  change ((squareTriangle 0).app (Opposite.op ⦋n⦌) a).1 =
    (stdSimplex.σ (0 : Fin 2)).app (Opposite.op ⦋n⦌) a at ht
  change ((squareTriangle 0).app (Opposite.op ⦋n⦌) a).2 =
    (stdSimplex.σ (1 : Fin 2)).app (Opposite.op ⦋n⦌) a at hb
  unfold coherentCompositionFixedTriangle coherentCompositionTriangle squarePrismTriangle
  change _ = (coherentCompositionSquare _ _ _).app (Opposite.op ⦋n⦌)
    (((squareTriangle 0).app (Opposite.op ⦋n⦌) a).1,
      (((squareTriangle 0).app (Opposite.op ⦋n⦌) a).2, _))
  rw [ht, hb]
  exact (coherentCompositionSquare_evaluate_cut
    (X := cocartesianTransportDiagramValue F (ULift.up 0))
    (Y := cocartesianTransportDiagramValue G (ULift.up 0))
    (Z := cocartesianTransportDiagramValue G (ULift.up 1))
    ((quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))).app
      (Opposite.op ⦋n⦌) s)
    (PinchedHom.constant (SimplicialCategory.homEquiv'
      (cocartesianTransportDiagramValue G (ULift.up 0))
      (cocartesianTransportDiagramValue G (ULift.up 1))
      (G.val.map strictIntervalIndexArrow)) n)
    ((stdSimplex.σ (0 : Fin 2)).app (Opposite.op ⦋n⦌) a)
    ((stdSimplex.σ (1 : Fin 2)).app (Opposite.op ⦋n⦌) a)).symm

end SerrePositivity.InfinityCategories
