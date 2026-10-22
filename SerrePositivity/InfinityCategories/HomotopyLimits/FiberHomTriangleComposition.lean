module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTriangleFiberTransport

/-!
概要：元の全 fiber Hom 比較は coherent な三角形の全族の合成と両立する。
方針：元の同じ三角形を各点で評価し、元の二辺の輸送族の合成を使う。
規約：写像空間全体の関手同型を構成し、個々の変換での合成同型に弱めない。
使われ方：Yoneda の元の前合成族と、恒等点評価の第一変数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全 fiber Hom 比較の合成則を、同じ coherent 三角形の全族で証明する。 -/
def unstraighteningFiberHom_triangleIso {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (t₀₁ : K ⟶ leftUnstraighteningTransformationSpace F G)
    (t₁₂ : K ⟶ leftUnstraighteningTransformationSpace G J)
    (t₀₂ : K ⟶ leftUnstraighteningTransformationSpace F J)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₂ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram t₀₁)
    (h₀ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram t₁₂)
    (h₁ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram t₀₂) (b : B _⦋0⦌) :
    FunctorIso (t₀₂ ≫ leftUnstraighteningMappingFiberHom F J b)
      (lift (t₀₁ ≫ leftUnstraighteningMappingFiberHom F G b)
        (t₁₂ ≫ leftUnstraighteningMappingFiberHom G J b) ≫
        MonoidalClosed.comp
          (vertexFiber pointedSpaceProjection (F.app _ b))
          (vertexFiber pointedSpaceProjection (G.app _ b))
          (vertexFiber pointedSpaceProjection (J.app _ b))) := by
  let U := coherentTriangleFiberTransportFamily F G H b 2 t₀₁ h₂
  let V := coherentTriangleFiberTransportFamily G J H b 0 t₁₂ h₀
  let W := coherentTriangleFiberTransportFamily F J H b 1 t₀₂ h₁
  have hc : prismEndpoint 1 K ≫
      ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ coherentTriangleEvaluate H b) =
      SSet.const (J.app _ b) := by
    rw [coherentTriangleEvaluate_edge H b 1 t₀₂ h₁, ← Category.assoc,
      intervalMappingUncurry_one, SSet.const_comp, evaluateFunctorAt_functorVertex]
  have h := fiberTransportFamilyTriangle_mapIso pointedSpaceProjection
    (coherentTriangleEvaluate H b) U V W hc
  simpa only [U, V, W, coherentTriangleFiberTransportFamily_map] using h

/-- 元の任意の二つの変換族は、全 fiber 作用の合成と両立する同じ三角形族へ延長できる。 -/
lemma unstraighteningFiberHom_compositionFamily_exists {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (t₀₁ : K ⟶ leftUnstraighteningTransformationSpace F G)
    (t₁₂ : K ⟶ leftUnstraighteningTransformationSpace G J) (b : B _⦋0⦌) :
    ∃ (t₀₂ : K ⟶ leftUnstraighteningTransformationSpace F J)
      (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}),
      (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram t₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram t₁₂ ∧
      (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram t₀₂ ∧
      Nonempty (FunctorIso (t₀₂ ≫ leftUnstraighteningMappingFiberHom F J b)
        (lift (t₀₁ ≫ leftUnstraighteningMappingFiberHom F G b)
          (t₁₂ ≫ leftUnstraighteningMappingFiberHom G J b) ≫
          MonoidalClosed.comp
            (vertexFiber pointedSpaceProjection (F.app _ b))
            (vertexFiber pointedSpaceProjection (G.app _ b))
            (vertexFiber pointedSpaceProjection (J.app _ b)))) := by
  obtain ⟨t₀₂, H, h₂, h₀, h₁⟩ := coherentTransformationFamilyTriangle_nonempty t₀₁ t₁₂
  exact ⟨t₀₂, H, h₂, h₀, h₁,
    ⟨unstraighteningFiberHom_triangleIso F G J t₀₁ t₁₂ t₀₂ H h₂ h₀ h₁ b⟩⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
