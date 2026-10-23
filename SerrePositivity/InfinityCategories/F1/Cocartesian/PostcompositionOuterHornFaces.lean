module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionOuterHorn
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleComponent

/-!
概要：後合成 fiber からの外ホーン比較の可変辺を、元の標準 Hom 比較で表示する。
方針：第二三角形の可変辺の式と、同じ source fiber の同型の零成分の式を合成する。
規約：元の fiber の包含と標準比較の全パラメーターを保持する。
使われ方：標準 Hom 比較と後合成 fiber の同値を用いる残りの局所比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "v" => NatTrans.app
  (coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1))) (Opposite.op ⦋0⦌) b
local notation "q" => cocartesianIntervalOuterHornMap F G v
local notation "r" => NatTrans.app (pre (SSet.Subcomplex.ι (horn 2 2))) CatInfinity
local notation "p₀" => quasicategoryCoreMap (CategoryTheory.Functor.map
  (ihom (F.val.obj (ULift.up 0))) (G.val.map strictIntervalIndexArrow))
local notation "b₀" => NatTrans.app (quasicategoryCoreMap
  (NatTrans.app (pre (F.val.map strictIntervalIndexArrow)) (G.val.obj (ULift.up 1))))
  (Opposite.op ⦋0⦌) b.down

/-- 同じ外ホーン比較の可変辺は、元の後合成 fiber の包含の後の標準 Hom 比較。 -/
lemma cocartesianPostcompositionOuterHornComparison_first :
    (stdSimplex.δ (2 : Fin 3) ▷
        (SSet.uliftFunctor.{u + 1, u}).obj (cocartesianIntervalPostcompositionFiber F G b)) ≫
        uncurry (cocartesianPostcompositionOuterHornComparison F G b ≫
          vertexFiberι r (NatTrans.app q (Opposite.op ⦋0⦌)
            (cocartesianIntervalSourceCompositionVertex F G b))) =
      intervalMappingUncurry ((SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p₀ b₀) ≫
        coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 0))
          (cocartesianTransportDiagramValue G (ULift.up 0))) := by
  rw [cocartesianPostcompositionOuterHornComparison_second, uncurry_natural_left,
    cocartesianIntervalSecondTriangleMap_uncurry]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    cocartesianHomFixedComponentComparison_secondTriangle_first,
    ← intervalMappingUncurry_precomp]
  congr 1
  simpa only [Category.assoc] using congrArg
    (fun h ↦ h ≫ coherentHomIntervalComparison
      (cocartesianTransportDiagramValue F (ULift.up 0))
      (cocartesianTransportDiagramValue G (ULift.up 0)))
    (cocartesianHomSourcePostcompositionFiberIso_inv_component_zero F G b)

end SerrePositivity.InfinityCategories
