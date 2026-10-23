module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTriangleRelativeVertex

/-!
概要：指定 coherent 三角形の全空間作用を元の実際の二射の合成へ比較する。
方針：全族の三角形比較を零単体で評価し、相対頂点の厳密な合成式を使う。
規約：三辺と三角形を変更しない。使われ方：標的の単位との合成の指定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定三角形の長辺の実際の全空間射は二辺の実際の射の合成と同型。
方針：同じ三角形の全族の比較を評価し相対写像空間に含める。
規約：三辺の作用を選び直さない。使われ方：元の coherent 変換と単位の合成。 -/
def unstraighteningTriangleVertexIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
    (z : (leftUnstraighteningTransformationSpace F J) _⦋0⦌)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const x))
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const y))
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const z)) :
    FunctorIso (leftUnstraighteningMappingVertexMap F J z).val
      ((leftUnstraighteningMappingVertexMap F G x).val ≫
        (leftUnstraighteningMappingVertexMap G J y).val) := by
  exact VertexIso.map
    (unstraighteningTriangleRelativeVertexIso F G J x y z H h₀₁ h₁₂ h₀₂)
    (vertexFiberι ((ihom (leftUnstraightening F)).map (leftUnstraighteningProjection J))
      (functorVertex (leftUnstraighteningProjection F)))

end SerrePositivity.InfinityCategories.F2
