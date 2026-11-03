module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedUniversalLift
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionUniversalInitial
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomotopyParameterizedPrism

/-!
概要：元の全三単体の第一辺を、同じ全パラメータの実 pointed prism として取り出す。
方針：実持ち上げを辺へ制限し、元の初期値と指定ホモトピーの底を厳密に回収する。
規約：元の第一辺の持ち上げを保持。使われ方：既存の指定始域比較への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3)

/-- 元の全三単体の第一辺の実持ち上げを、その全選択とともに保持する。 -/
def coherentColimitUnitPointedFirstEdge :=
  (((stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ▷ leftUnstraightening F) ▷
    coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      coherentColimitUnitPointedTetrahedronUniversalLift B T k

/-- 元の第一辺の実持ち上げの始点は、元の pointed 始点の同じ全パラメータ族。 -/
lemma coherentColimitUnitPointedFirstEdge_source :
    (prismEndpoint 0 (leftUnstraightening F) ▷
      coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        coherentColimitUnitPointedFirstEdge B T k =
      fst (leftUnstraightening F) (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        pullback.fst pointedSpaceProjection F := by
  have he : scaffoldFirstVertex.{u + 1} 1 ≫
      (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) = scaffoldFirstVertex 3 := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro x
    rfl
  apply simplexPrism_initialRestriction 1
  rw [coherentColimitUnitPointedFirstEdge, ← Category.assoc,
    ← comp_whiskerRight, ← comp_whiskerRight, he]
  exact relativeExtensionUniversal_initial pointedSpaceProjection
    ((Δ[3] ◁ leftUnstraighteningProjection F) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k)
    (scaffoldFirstVertex 3 ▷ leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F 3 _
      (coherentColimitUnitPointedTetrahedronDiagram_initial B T k))

/-- 第一辺が指定円柱と一致すれば、実 prism の底も同じ指定変換族の底に厳密に一致。 -/
lemma coherentColimitUnitPointedFirstEdge_projection
    {Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F Q)
    (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h) :
    coherentColimitUnitPointedFirstEdge B T k ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷
        coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      functorParameterizedPrism (intervalMappingUncurry
        (SSet.const (coherentVertexOfHomotopy H))) := by
  have hd : ((stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj B) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k =
        functorSimplexDiagram (curry H.h) := by
    rw [coherentColimitUnitPointedTetrahedronDiagram, functorSimplexDiagram_pre, he]
  rw [coherentColimitUnitPointedFirstEdge, Category.assoc,
    coherentColimitUnitPointedTetrahedronUniversalLift_projection,
    coherentVertexOfHomotopy_parameterizedPrism, ← hd]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
