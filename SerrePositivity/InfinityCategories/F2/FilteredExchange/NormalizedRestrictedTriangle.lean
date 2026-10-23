module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RestrictedTriangleEndpoint

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
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {B C : SSet.{u + 1}}
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
      coherentTransformationFamilyDiagram (SSet.const z))

local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "w" => unstraighteningMappingTriangleLongWitness F G J
  (SSet.const x) (SSet.const y) (SSet.const z) H h₀₁ h₁₂ h₀₂

variable (s : C ⟶ leftUnstraightening F)
local notation "P" => relativeFunctorPre (leftUnstraighteningProjection J)
  (leftUnstraighteningProjection F) s
local notation "c" => unstraighteningIdentityRestrictedEndpointIso F J (SSet.const z)
  (UnstraighteningFamilyWitness.prism w) (UnstraighteningFamilyWitness.source w)
  (UnstraighteningFamilyWitness.projection w) l s
local notation "e" => unstraighteningTriangleRelativeVertexIso F G J x y z H h₀₁ h₁₂ h₀₂

/-- 同じ二 prism の局所指定比較を、元の三角形比較の両端の実頂点へ正規化する。 -/
def normalizedRestrictedTriangleIso :
    VertexIso ((P).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (leftUnstraighteningMappingVertexMap F J z).val
        (leftUnstraighteningMappingVertexMap F J z).property))
      ((P).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
          ((leftUnstraighteningMappingVertexMap F G x).val ≫
            (leftUnstraighteningMappingVertexMap G J y).val)
          (by rw [Category.assoc, (leftUnstraighteningMappingVertexMap G J y).property,
            (leftUnstraighteningMappingVertexMap F G x).property]))) := by
  have hs := (restrictedUniversalEndpoint_vertex F J z l s).trans
    (relativeFunctorPre_vertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
      s (leftUnstraighteningMappingVertexMap F J z).val
      (leftUnstraighteningMappingVertexMap F J z).property).symm
  have ht := (restrictedTriangleEndpoint_vertex F G J x y z H h₀₁ h₁₂ h₀₂ s).trans
    (relativeFunctorPre_vertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
      s ((leftUnstraighteningMappingVertexMap F G x).val ≫
        (leftUnstraighteningMappingVertexMap G J y).val)
      (by rw [Category.assoc, (leftUnstraighteningMappingVertexMap G J y).property,
        (leftUnstraighteningMappingVertexMap F G x).property])).symm
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hs)).symm ≪≫ c ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk ht)

/-- 両端の正規化を外すと同じ二つの実 prism の指定比較を回収する。 -/
lemma normalizedRestrictedTriangleIso_heq :
    HEq (normalizedRestrictedTriangleIso F G J x y z H h₀₁ h₁₂ h₀₂ s) c := by
  unfold normalizedRestrictedTriangleIso
  dsimp only
  exact iso_endpoints_heq _ _ _

/-- 元の実際の相対三角形比較の制限と局所指定比較の正規化は等しい。 -/
lemma unstraighteningTriangleRelativeVertexIso_pre_eq :
    VertexIso.map e P = normalizedRestrictedTriangleIso F G J x y z H h₀₁ h₁₂ h₀₂ s := by
  exact eq_of_heq ((unstraighteningTriangleRelativeVertexIso_pre F G J
    x y z H h₀₁ h₁₂ h₀₂ s).trans
      (normalizedRestrictedTriangleIso_heq F G J x y z H h₀₁ h₁₂ h₀₂ s).symm)

end SerrePositivity.InfinityCategories.F2
