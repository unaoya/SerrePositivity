module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleCanonicalEvaluation
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalTriangleNaturality

/-!
概要：元の固定成分比較の第二三角形は、同じ零成分からの coherent 合成三角形の族。
方針：元の prism の全単体評価と、同じ切断した第二三角形の一致を使う。
規約：元の比較射と全パラメーターを保持する。
使われ方：元の固定成分比較を証明済みの標準 fiber 同値へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "v" => NatTrans.app
  (coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1))) (Opposite.op ⦋0⦌) b
local notation "S" => vertexFiber (cocartesianHomSourceComponent F G (ULift.up 1)) b

/-- 元の第二三角形の全体は、元の零成分と終域輸送の標準合成三角形の族。 -/
lemma cocartesianHomFixedComponentComparison_secondTriangle :
    cocartesianIntervalHomTriangle F G v 1
        (cocartesianHomFixedComponentComparison F G (ULift.up 1) b) =
      (Δ[2] ◁ (vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))))) ≫
      coherentCompositionFixedTriangle
        (cocartesianTransportDiagramValue F (ULift.up 0))
        (cocartesianTransportDiagramValue G (ULift.up 0))
        (cocartesianTransportDiagramValue G (ULift.up 1))
        (show cocartesianTransportDiagramValue G (ULift.up 0) ⟶
          cocartesianTransportDiagramValue G (ULift.up 1) from G.val.map strictIntervalIndexArrow) := by
  unfold cocartesianIntervalHomTriangle cocartesianIntervalHomSquare
  rw [cocartesianHomFixedComponentComparison_prism]
  rw [← intervalFunctorHomPrism_precomp
    (vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b)
    (cocartesianTransportDiagramHomInterval F G)]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  have ht := congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌) a) (squareTriangle_one_time.{u + 1})
  have hb := congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌) a) (squareTriangle_one_base.{u + 1})
  change ((squareTriangle 1).app (Opposite.op ⦋n⦌) a).1 =
    (stdSimplex.σ (1 : Fin 2)).app (Opposite.op ⦋n⦌) a at ht
  change ((squareTriangle 1).app (Opposite.op ⦋n⦌) a).2 =
    (stdSimplex.σ (0 : Fin 2)).app (Opposite.op ⦋n⦌) a at hb
  change (intervalFunctorHomPrism (cocartesianTransportDiagramHomInterval F G)).app
    (Opposite.op ⦋n⦌)
    ((((squareTriangle 1).app (Opposite.op ⦋n⦌) a).1,
      (localKanDiagramBaseIso 1).hom.app (Opposite.op ⦋n⦌)
        (((squareTriangle 1).app (Opposite.op ⦋n⦌) a).2)), s.val) = _
  rw [ht, hb]
  change (intervalFunctorHomPrism (cocartesianTransportDiagramHomInterval F G)).app
    (Opposite.op ⦋n⦌) (((stdSimplex.σ (1 : Fin 2)).app (Opposite.op ⦋n⦌) a,
      ULift.up (cocartesianSecondTriangleBaseSimplex a)), ULift.up s.val.down) = _
  rw [cocartesianTransportDiagramHomIntervalPrism_evaluate_cut]
  change cocartesianSecondTriangleCutSimplex F G a s.val.down = _
  rw [cocartesianSecondTriangleCutSimplex_eq_canonical,
    cocartesianSecondTriangleCanonicalSimplex_eq_evaluation]
  rfl

end SerrePositivity.InfinityCategories
