module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FixedComponentCompositionFiber

/-!
概要：元の比較の第二三角形の可変辺を、元の零成分の標準 Hom 比較へ接続する。
方針：同じ正方形の底辺を成分評価で読み、元の Hom 作用の評価の可換式を使う。
規約：元の比較射と零成分の全高次の作用を保持する。
使われ方：元の後合成 fiber と外ホーン延長 fiber の同じ作用での比較。
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

/-- 元の比較の第二三角形の前辺は、元の零成分への標準の coherent Hom 比較。 -/
lemma cocartesianHomFixedComponentComparison_secondTriangle_first :
    (stdSimplex.δ (2 : Fin 3) ▷ S) ≫ cocartesianIntervalHomTriangle F G v 1
        (cocartesianHomFixedComponentComparison F G (ULift.up 1) b) =
      intervalMappingUncurry
        (vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            (quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))) ≫
          coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 0))
            (cocartesianTransportDiagramValue G (ULift.up 0))) := by
  unfold cocartesianIntervalHomTriangle
  rw [← Category.assoc, ← comp_whiskerRight, triangleSquare_lower_bottom]
  unfold cocartesianIntervalHomSquare
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((lift (𝟙 (Δ[1] : SSet.{u + 1}))
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      (Δ[1] ◁ (localKanDiagramBaseIso 1).hom)) ▷ S) ≫ _ = _
  rw [localIntervalDiagramBaseIso_side, cocartesianHomFixedComponentComparison_prism]
  rw [intervalFunctorHomPrism_evaluateOfEq
    (x := coherentNerveVertex (cocartesianTransportDiagramValue F (ULift.up 0)))
    (y := coherentNerveVertex (cocartesianTransportDiagramValue G (ULift.up 0)))
    (vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b ≫
      cocartesianTransportDiagramHomInterval F G)
    (ULift.up (nerveVertex (ULift.up (0 : Fin 2))))
    (by simpa only [evaluateFunctorAt_functorVertex, cocartesianTransportDiagramValueFunctor] using
      qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor F) (ULift.up 0))
    (by simpa only [evaluateFunctorAt_functorVertex, cocartesianTransportDiagramValueFunctor] using
      qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor G) (ULift.up 0))]
  change intervalMappingUncurry
    ((vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b ≫
      cocartesianTransportDiagramHomInterval F G) ≫
        cocartesianHomIntervalEvaluation F G (ULift.up 0)) = _
  rw [Category.assoc, cocartesianTransportDiagramHomInterval_evaluation]
  rfl

end SerrePositivity.InfinityCategories
