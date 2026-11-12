module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningMappingTrianglePrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramTransportComparisonValue

/-!
概要：元の定値図式の全三角形の長辺証拠を、同じ区間の pointed 輸送として保持する。
方針：元の全持ち上げから取り出した長辺証拠を、そのまま定値図式の座標で読む。
規約：全三角形と二辺の元の作用を保持。使われ方：下側の指定輸送因子への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} {x y z : SpaceInfinity.{u} _⦋0⦌}
  (a : K ⟶ intervalMappingSpace x y) (b : K ⟶ intervalMappingSpace y z)
  (c : K ⟶ intervalMappingSpace x z)
local notation "A" => constantDiagramTransformation B a
local notation "D" => constantDiagramTransformation B b
local notation "C" => constantDiagramTransformation B c
variable (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
  (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram (constantDiagramTransformation B a))
  (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram (constantDiagramTransformation B b))
  (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram (constantDiagramTransformation B c))

/-- 元の全三角形の指定長辺証拠を、元の長区間の全輸送として保持する。 -/
def constantDiagramTriangleLongTransport :
    FiberTransportFamily (b := z) pointedSpaceProjection
      (constantUnstraighteningFiberProjection B x) (intervalMappingUncurry c) :=
  constantDiagramTransportWitness (unstraighteningMappingTriangleLongWitness
    (SSet.const x : B ⟶ SpaceInfinity) (SSet.const y) (SSet.const z) A D C H h₀₁ h₁₂ h₀₂)

/-- 元の定値長辺の指定比較へ、元の全三角形の長辺証拠をそのまま入力できる。 -/
lemma constantDiagramMappingTransportIso_heq_triangle :
    HEq (constantDiagramMappingTransportIso B c)
      ((constantDiagramTransportWitness (constantDiagramMappingFamilyWitness B c)).endpointIso
        pointedSpaceProjection (constantUnstraighteningFiberProjection B x)
        (intervalMappingUncurry c) (intervalMappingUncurry_one c)
        (constantDiagramTriangleLongTransport a b c H h₀₁ h₁₂ h₀₂) ≪≫
          pointedIntervalTransportComparison (constantUnstraighteningFiberProjection B x) c
            (constantDiagramTriangleLongTransport a b c H h₀₁ h₁₂ h₀₂)) :=
  constantDiagramMappingTransportIso_heq_via B c
    (constantDiagramTriangleLongTransport a b c H h₀₁ h₁₂ h₀₂)

end SerrePositivity.InfinityCategories.F2
