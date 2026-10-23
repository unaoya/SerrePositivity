module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeTriangleVertexPresentation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTriangleExtensionComparison

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

variable {B : SSet.{u + 1}}
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

/-- 元の相対頂点比較は任意の始域制限後に同じ二 prism の指定終点比較となる。 -/
lemma unstraighteningTriangleRelativeVertexIso_pre {C : SSet.{u + 1}}
    (s : C ⟶ leftUnstraightening F) :
    HEq
      (VertexIso.map (unstraighteningTriangleRelativeVertexIso F G J x y z H h₀₁ h₁₂ h₀₂)
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s))
      (unstraighteningIdentityRestrictedEndpointIso F J (SSet.const z)
        (w).prism (w).source (w).projection l s) := by
  exact (unstraighteningTriangleRelativeVertexIso_map_pre_heq_component F G J
    x y z H h₀₁ h₁₂ h₀₂ s).trans
      (unstraighteningMappingTriangleIso_app_pre F G J (SSet.const x) (SSet.const y)
        (SSet.const z) H h₀₁ h₁₂ h₀₂ l s)

end SerrePositivity.InfinityCategories.F2
