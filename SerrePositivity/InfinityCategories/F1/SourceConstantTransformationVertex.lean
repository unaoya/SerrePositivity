module

public import SerrePositivity.InfinityCategories.F1.SourceConstantTransformationNaturality
public import SerrePositivity.InfinityCategories.F1.HomotopyFatCone
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.F1.IntervalMappingVertexEquivalence

/-!
概要：変換空間の指定頂点の円柱・fat join 表示と、そこから回収したホモトピーを同定する。
方針：Yoneda 族の二回の uncurry と辺・頂点の厳密な往復を使う。
規約：元の指定変換を選び直さない。
使われ方：全空間錐の実現の比較を元の単位の変換へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：指定した関手の辺の変換頂点の円柱は、元の辺のホモトピーの円柱。
方針：頂点の Yoneda 族を二度 uncurry する。
規約：右の一点のパラメータだけを忘れる。使われ方：指定辺の厳密な追跡。 -/
lemma sourceConstantTransformationPrism_of_edge
    (e : SSet.Edge (X := (ihom K).obj X) (functorVertex (SSet.const z)) (functorVertex f)) :
    sourceConstantTransformationPrism (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e)) =
      fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫
        (simplicialHomotopyOfFunctorEdge e.toTruncated).h := by
  rw [sourceConstantTransformationPrism, intervalMappingUncurry, SSet.yonedaEquiv_symm_comp]
  change (α_ K (Δ[1] : SSet.{u}) Δ[0]).hom ≫
      uncurry (uncurry (SSet.yonedaEquiv.symm
        (functorVertex (SSet.yonedaEquiv.symm e.edge)))) = _
  rw [uncurry_yoneda_functorVertex, uncurry_natural_left]
  rfl

/-- 概要：任意の指定変換の頂点の円柱は、その回収ホモトピーの円柱そのもの。
方針：辺と変換頂点の全単射で指定辺へ戻す。
規約：両端も指定変換も同じ。使われ方：元の単位の実現との整合性。 -/
lemma sourceConstantTransformationPrism_vertex
    (t : (intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) _⦋0⦌) :
    sourceConstantTransformationPrism (SSet.yonedaEquiv.symm t) =
      fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫
        (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated).h := by
  obtain ⟨e, rfl⟩ := (intervalMappingEdgeVertexEquiv (functorVertex (SSet.const z))
    (functorVertex f)).surjective t
  change sourceConstantTransformationPrism
      (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e)) =
    fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫
      (simplicialHomotopyOfFunctorEdge
        (intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge e)).toTruncated).h
  rw [show intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge e) = e from
    (intervalMappingEdgeVertexEquiv (functorVertex (SSet.const z))
      (functorVertex f)).symm_apply_apply e]
  exact sourceConstantTransformationPrism_of_edge e

end SerrePositivity.InfinityCategories
