module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalPrecompositionTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiberHomTriangleComposition

/-!
概要：選択済みの元の区間 Hom 前合成と、元の全 fiber Hom 作用の合成を比較する。
方針：同じ前合成を長辺に持つ三角形の全族を、同じ共同評価へ送る。
規約：元の前合成と指定辺を保持し、別の合成代表の存在だけで済ませない。
使われ方：Yoneda 評価の第一変数の全パラメータ自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の関手空間内の三角形族を、同じ共同評価の三角形族へ移す。 -/
def coherentFunctorTriangleDiagram {B K : SSet.{u + 1}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ (ihom B).obj SpaceInfinity.{u}) :
    (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u} :=
  (α_ Δ[2] B K).inv ≫ functorParameterizedPrism H

/-- 共同評価へ移しても、三辺は元の同じ区間族の共同評価。 -/
lemma coherentFunctorTriangleDiagram_edge {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ (ihom B).obj SpaceInfinity.{u})
    (i : Fin 3) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (hi : (stdSimplex.δ i ▷ K) ≫ H = intervalMappingUncurry t) :
    (stdSimplex.δ i ▷ (B ⊗ K)) ≫ coherentFunctorTriangleDiagram H =
      coherentTransformationFamilyDiagram t := by
  rw [coherentTransformationFamilyDiagram, ← hi]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨i, b, k⟩
  rfl

/-- 選択済みの元の区間 Hom 前合成は、同じ指定辺と全 fiber Hom の作用の合成に両立。 -/
def unstraighteningFiberHom_precomposeIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    FunctorIso
      (intervalPrecompose (functorVertex J)
        (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
          leftUnstraighteningMappingFiberHom F J b)
      (lift (SSet.const (intervalMappingVertexOfEdge e) ≫
          leftUnstraighteningMappingFiberHom F G b)
        (leftUnstraighteningMappingFiberHom G J b) ≫
        MonoidalClosed.comp
          (vertexFiber pointedSpaceProjection (F.app _ b))
          (vertexFiber pointedSpaceProjection (G.app _ b))
          (vertexFiber pointedSpaceProjection (J.app _ b))) := by
  let hex := intervalPrecompose_triangleFamily_exists e (functorVertex J)
  let H := hex.choose
  have h₂ := hex.choose_spec.1
  have h₀ := hex.choose_spec.2.1
  have h₁ := hex.choose_spec.2.2
  have h := unstraighteningFiberHom_triangleIso F G J
    (SSet.const (intervalMappingVertexOfEdge e)) (𝟙 _)
    (intervalPrecompose (functorVertex J)
      (SSet.Truncated.HomotopyCategory.homMk e.toTruncated))
    (coherentFunctorTriangleDiagram H)
    (coherentFunctorTriangleDiagram_edge H 2 _ h₂)
    (coherentFunctorTriangleDiagram_edge H 0 _ h₀)
    (coherentFunctorTriangleDiagram_edge H 1 _ h₁) b
  simpa only [Category.id_comp] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
