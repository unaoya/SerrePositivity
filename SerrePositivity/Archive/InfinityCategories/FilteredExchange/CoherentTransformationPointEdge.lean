module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence

/-!
概要：元の coherent 変換の一点評価を実際の関手辺の一点評価と同定する。
方針：変換頂点と辺の全単射を使い、同じ評価を次数ごとに計算する。
規約：元の一次単体そのものを保持。使われ方：元の各点の錐と fiber transport の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の変換の全族の一点への制限は元の関手辺の指定評価と厳密に等しい。
方針：頂点を辺の表示へ戻し、全次数の評価の定義を計算する。
規約：同値類でなく射の等式。使われ方：元の三角形の三辺を各点で識別。 -/
lemma coherentTransformationPointDiagram_edge {B : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}}
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌) :
    coherentTransformationPointDiagram (coherentTransformationFamilyDiagram (SSet.const x)) b =
      SSet.yonedaEquiv.symm (functorEdgeAt (intervalMappingEdgeOfVertex x) b).edge := by
  let e := intervalMappingEdgeOfVertex x
  have hx : intervalMappingVertexOfEdge e = x :=
    (intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).apply_symm_apply x
  calc
    _ = coherentTransformationPointDiagram
        (coherentTransformationFamilyDiagram (SSet.const (intervalMappingVertexOfEdge e))) b :=
      congrArg (fun z : (leftUnstraighteningTransformationSpace F G) _⦋0⦌ =>
        coherentTransformationPointDiagram (coherentTransformationFamilyDiagram (SSet.const z)) b)
        hx.symm
    _ = _ := by
      unfold coherentTransformationPointDiagram coherentTransformationFamilyDiagram
        intervalMappingUncurry
      rw [SSet.const_comp]
      change _ ≫ _ ≫ functorParameterizedPrism (MonoidalClosed.uncurry
        (SSet.const (functorVertex (SSet.yonedaEquiv.symm e.edge)))) = _
      rw [uncurry_const_functorVertex]
      change _ = SSet.yonedaEquiv.symm ((evaluateFunctorAt b).app _ e.edge)
      rw [← SSet.yonedaEquiv_symm_comp]
      unfold functorParameterizedPrism
      rw [MonoidalClosed.uncurry_natural_left]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      rfl

end SerrePositivity.InfinityCategories.F2
