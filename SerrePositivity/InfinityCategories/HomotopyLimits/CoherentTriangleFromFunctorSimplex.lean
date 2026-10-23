module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransformationPoint
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismTriangles

/-!
概要：元の関手空間の合成二単体を、同じ三辺の coherent 変換の全三角形にする。
方針：同じ二単体の評価 prism に一点パラメーターを足し、三面を厳密に照合する。
規約：長辺を充填で選び直さず、元の全二単体と全三辺を保持する。
使われ方：元の全錐の各脚の合成三角形を、全空間作用・指定余錐比較へ入力する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の辺の区間頂点による変換図式は、同じ元の辺の評価 prism。 -/
lemma coherentTransformationFamilyDiagram_of_edge {B : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}}
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    coherentTransformationFamilyDiagram
      (SSet.const (intervalMappingVertexOfEdge e) : (Δ[0] : SSet.{u + 1}) ⟶ _) =
        (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫ functorEdgePrism e := by
  rw [coherentTransformationFamilyDiagram_const_prism,
    show intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge e) = e from
      (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]

/-- 一点パラメーター付きの三角形評価の各面は、元の同じ評価の各面。 -/
lemma functorTrianglePrismPoint_face {B X : SSet.{u + 1}}
    (q : (Δ[2] : SSet.{u + 1}) ⟶ (ihom B).obj X) (i : Fin 3) :
    (stdSimplex.δ i ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫
      ((Δ[2] : SSet.{u + 1}) ◁ fst B (Δ[0] : SSet.{u + 1})) ≫ functorFamilyPrism q =
    (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫
      (stdSimplex.δ i ▷ B) ≫ functorFamilyPrism q := rfl

/-- 元の関手空間の同じ合成二単体を、元の三辺を持つ全変換三角形へ移す。 -/
def coherentTransformationTriangleOfFunctorSimplex {B : SSet.{u + 1}}
    {F G J : B ⟶ SpaceInfinity.{u}}
    {e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)}
    {f : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex G) (functorVertex J)}
    {g : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex J)}
    (σ : SSet.Truncated.Edge.CompStruct e.toTruncated f.toTruncated g.toTruncated) :
    F2.CoherentTransformationVertexTriangle F G J
      (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f) where
  diagonal := intervalMappingVertexOfEdge g
  diagram := (Δ[2] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫
    functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex)
  first := by
    rw [functorTrianglePrismPoint_face, functorCompStructPrism_two σ,
      coherentTransformationFamilyDiagram_of_edge]
    rfl
  second := by
    rw [functorTrianglePrismPoint_face, functorCompStructPrism_zero σ,
      coherentTransformationFamilyDiagram_of_edge]
    rfl
  long := by
    rw [functorTrianglePrismPoint_face, functorCompStructPrism_one σ,
      coherentTransformationFamilyDiagram_of_edge]
    rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
