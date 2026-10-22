module

public import SerrePositivity.InfinityCategories.F2.ConstantDiagramSourceComparison
public import SerrePositivity.InfinityCategories.F2.ConstantDiagramTriangleTransport
public import SerrePositivity.InfinityCategories.F2.UnstraighteningTriangleComparisonPresentation

/-!
概要：元の定値図式の指定三角形比較を、同じ長辺の実輸送の endpointIso へ同定する。
方針：元の長辺証拠の始域付き比較へ戻し、その定値 fiber 像を計算する。
規約：三辺・全三角形・元の比較を保持。使われ方：下側輸送因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} {x y z : SpaceInfinity.{u} _⦋0⦌}
  (a : K ⟶ intervalMappingSpace x y) (b : K ⟶ intervalMappingSpace y z)
  (c : K ⟶ intervalMappingSpace x z)
local notation "F" => (SSet.const x : B ⟶ SpaceInfinity)
local notation "G" => (SSet.const y : B ⟶ SpaceInfinity)
local notation "J" => (SSet.const z : B ⟶ SpaceInfinity)
local notation "E" => leftUnstraightening F
local notation "q" => leftUnstraighteningProjection F
local notation "A" => constantDiagramTransformation B a
local notation "D" => constantDiagramTransformation B b
local notation "C" => constantDiagramTransformation B c

/-- 元の三角形比較の定値 fiber 像は、同じ実長辺輸送への指定比較の全 curry。 -/
lemma constantDiagramTriangleComparison_heq_fiber
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram A)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram D)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram C) :
    HEq ((unstraighteningMappingTriangleIso F G J A D C H h₀₁ h₁₂ h₀₂).postcomp
      (constantUnstraighteningRelativeIso q z).hom)
      (VertexIso.map
        ((constantDiagramTransportWitness (constantDiagramMappingFamilyWitness B c)).endpointIso
          pointedSpaceProjection (constantUnstraighteningFiberProjection B x)
          (intervalMappingUncurry c) (intervalMappingUncurry_one c)
          (constantDiagramTriangleLongTransport a b c H h₀₁ h₁₂ h₀₂))
        (functorSpaceCurryMap E K (vertexFiber pointedSpaceProjection z))) := by
  let f := relativeFunctorUncurry (A ≫ leftUnstraighteningMappingSpaceMap F G)
  let g := relativeFunctorUncurry (D ≫ leftUnstraighteningMappingSpaceMap G J)
  let h := lift f (snd E K) ≫ g
  let w := unstraighteningMappingTriangleLongWitness F G J A D C H h₀₁ h₁₂ h₀₂
  have hh := unstraighteningMappingComposite_projection F G J A D
  let e := unstraighteningSourceFamilyComparisonIso F J q (𝟙 E) (Category.id_comp _)
    C h hh w.prism w.source w.target w.projection
  have he := unstraighteningMappingTriangleIso_heq_source F G J A D C H h₀₁ h₁₂ h₀₂ hh
  have hs : (C ≫ leftUnstraighteningMappingSpaceMap F J) ≫
      relativeFunctorOverPre (leftUnstraighteningProjection J)
        (Over.homMk (U := Over.mk q) (V := Over.mk q) (𝟙 E) (Category.id_comp _)) =
      C ≫ leftUnstraighteningMappingSpaceMap F J := by
    change _ ≫ relativeFunctorOverPre _ (𝟙 _) = _
    rw [relativeFunctorOverPre_id, Category.comp_id]
  have ht : relativeFunctorCurry h hh =
      lift (A ≫ leftUnstraighteningMappingSpaceMap F G)
        (D ≫ leftUnstraighteningMappingSpaceMap G J) ≫
          relativeFunctorComposition (Over.mk q) (Over.mk (leftUnstraighteningProjection G))
            (Over.mk (leftUnstraighteningProjection J)) := by
    apply relativeFunctorUncurry_injective
    rw [relativeFunctorUncurry_curry]
    apply SSet.hom_ext
    intro n
    rfl
  refine (functorIso_postcomp_heq_of_heq e _ hs ht he
    (constantUnstraighteningRelativeIso q z).hom).trans ?_
  exact constantDiagramSourceComparison_heq_transport c h hh w

end SerrePositivity.InfinityCategories.F2
