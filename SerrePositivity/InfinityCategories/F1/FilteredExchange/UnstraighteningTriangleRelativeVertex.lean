module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.TransformationFamilyDiagram
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorComposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingInvertible
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.UnstraighteningTriangleComposition
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.UnstraighteningConstantVertices

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
  have hs := unstraighteningMappingConst_vertex F J z
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  have ht := unstraighteningMappingConstComposite_vertex F G J x y
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hs)).symm ≪≫ e ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk ht)

end SerrePositivity.InfinityCategories.F2
