module

public import SerrePositivity.InfinityCategories.F1.CocartesianFirstTriangleCanonical
public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalTriangleNaturality

/-!
概要：元の固定成分比較の第一三角形を、同じ指定合成三角形への定値族と同定する。
方針：元の比較の prism の式を全単体で評価し、切断した豊穣図式の一致を使う。
規約：元の比較射そのものと、固定成分の全パラメーターを保持する。
使われ方：指定第一三角形上の fiber へ元の比較を制限する。
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

/-- 元の固定成分比較の第一三角形全体は、同じ指定合成三角形への定値族。 -/
lemma cocartesianHomFixedComponentComparison_firstTriangle :
    cocartesianIntervalHomTriangle F G v 0
        (cocartesianHomFixedComponentComparison F G (ULift.up 1) b) =
      fst (Δ[2] : SSet.{u + 1}) S ≫
        SSet.yonedaEquiv.symm (cocartesianIntervalSourceCompStruct F G b).simplex := by
  unfold cocartesianIntervalHomTriangle cocartesianIntervalHomSquare
  rw [cocartesianHomFixedComponentComparison_prism]
  rw [← intervalFunctorHomPrism_precomp
    (vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b)
    (cocartesianTransportDiagramHomInterval F G)]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  have ht := congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌) a)
    (squareTriangle_zero_time.{u + 1})
  have hb := congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌) a)
    (squareTriangle_zero_base.{u + 1})
  change ((squareTriangle 0).app (Opposite.op ⦋n⦌) a).1 =
    (stdSimplex.σ (0 : Fin 2)).app (Opposite.op ⦋n⦌) a at ht
  change ((squareTriangle 0).app (Opposite.op ⦋n⦌) a).2 =
    (stdSimplex.σ (1 : Fin 2)).app (Opposite.op ⦋n⦌) a at hb
  change (intervalFunctorHomPrism (cocartesianTransportDiagramHomInterval F G)).app
    (Opposite.op ⦋n⦌)
    ((((squareTriangle 0).app (Opposite.op ⦋n⦌) a).1,
      (localKanDiagramBaseIso 1).hom.app (Opposite.op ⦋n⦌)
        (((squareTriangle 0).app (Opposite.op ⦋n⦌) a).2)), s.val) = _
  rw [ht, hb]
  change (intervalFunctorHomPrism (cocartesianTransportDiagramHomInterval F G)).app
    (Opposite.op ⦋n⦌) (((stdSimplex.σ (0 : Fin 2)).app (Opposite.op ⦋n⦌) a,
      ULift.up (cocartesianFirstTriangleBaseSimplex a)), ULift.up s.val.down) = _
  rw [cocartesianTransportDiagramHomIntervalPrism_evaluate_cut]
  change cocartesianFirstTriangleCutSimplex F G a s.val.down = _
  rw [cocartesianFirstTriangleCutSimplex_eq_canonical F G b a s,
    cocartesianFirstTriangleCanonicalSimplex_eq_map]
  rfl

end SerrePositivity.InfinityCategories
