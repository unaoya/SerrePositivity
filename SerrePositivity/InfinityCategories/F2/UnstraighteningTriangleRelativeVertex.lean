module

public import SerrePositivity.InfinityCategories.F2.UnstraighteningTriangleComposition
public import SerrePositivity.InfinityCategories.F2.RelativeFunctorCompositionVertex
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingInvertible

/-!
概要：指定 coherent 三角形の全空間作用を底を固定した相対写像空間内で比較する。
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
def unstraighteningTriangleRelativeVertexIso {B : SSet.{u + 1}}
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
    VertexIso (X := relativeFunctorSpace (leftUnstraighteningProjection J)
      (leftUnstraighteningProjection F))
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (leftUnstraighteningMappingVertexMap F J z).val
        (leftUnstraighteningMappingVertexMap F J z).property)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        ((leftUnstraighteningMappingVertexMap F G x).val ≫
          (leftUnstraighteningMappingVertexMap G J y).val)
        (by rw [Category.assoc, (leftUnstraighteningMappingVertexMap G J y).property,
          (leftUnstraighteningMappingVertexMap F G x).property])) := by
  have e := (unstraighteningMappingTriangleIso F G J
    (SSet.const x) (SSet.const y) (SSet.const z) H h₀₁ h₁₂ h₀₂).app
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  simp only [SSet.const_comp] at e
  have hconst {X A : SSet.{u + 1}} (v : X _⦋0⦌) (pt : A _⦋0⦌) :
      (SSet.const v : A ⟶ X).app (Opposite.op ⦋0⦌) pt = v := by
    change X.map _ v = v
    rw [show (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = 𝟙 (Opposite.op ⦋0⦌) from
      Subsingleton.elim _ _, X.map_id]
    rfl
  change VertexIso
    ((SSet.const ((leftUnstraighteningMappingSpaceMap F J).app (Opposite.op ⦋0⦌) z) :
      (Δ[0] : SSet.{u + 1}) ⟶ _).app (Opposite.op ⦋0⦌) _)
    ((relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
      (Over.mk (leftUnstraighteningProjection G)) (Over.mk (leftUnstraighteningProjection J))).app
        (Opposite.op ⦋0⦌)
          ((SSet.const ((leftUnstraighteningMappingSpaceMap F G).app _ x) :
            (Δ[0] : SSet.{u + 1}) ⟶ _).app (Opposite.op ⦋0⦌) _,
           (SSet.const ((leftUnstraighteningMappingSpaceMap G J).app _ y) :
            (Δ[0] : SSet.{u + 1}) ⟶ _).app (Opposite.op ⦋0⦌) _)) at e
  simp only [hconst] at e
  rw [← leftUnstraighteningMappingVertexMap_vertex F J z,
    ← leftUnstraighteningMappingVertexMap_vertex F G x,
    ← leftUnstraighteningMappingVertexMap_vertex G J y] at e
  have hc := relativeFunctorComposition_vertex
    (Over.mk (leftUnstraighteningProjection F)) (Over.mk (leftUnstraighteningProjection G))
    (Over.mk (leftUnstraighteningProjection J))
    (leftUnstraighteningMappingVertexMap F G x).val
    (leftUnstraighteningMappingVertexMap F G x).property
    (leftUnstraighteningMappingVertexMap G J y).val
    (leftUnstraighteningMappingVertexMap G J y).property
  have et := e ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hc)
  exact et

end SerrePositivity.InfinityCategories.F2
