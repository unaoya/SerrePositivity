module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramTriangleComparisonFiber
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramTransportMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPointComparison

/-!
概要：元の全三角形の比較の一点成分を、同じ実長辺輸送の指定比較の制限へ戻す。
方針：両実終点の全族を同定し、同じ指定 curry 比較を評価する。
規約：三辺と全二単体を保持。使われ方：元の定値余極限三角形の値の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} [Quasicategory K] {x y z : SpaceInfinity.{u} _⦋0⦌}
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

/-- 指定全三角形比較の各点成分は、同じ実長辺輸送への指定比較の同じ係数への制限。 -/
lemma constantDiagramTriangleComparison_app_heq_transport
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram A)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram D)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram C) (l : K _⦋0⦌) :
    HEq (((unstraighteningMappingTriangleIso F G J A D C H h₀₁ h₁₂ h₀₂).postcomp
      (constantUnstraighteningRelativeIso q z).hom).app l)
      (((constantDiagramTransportWitness (constantDiagramMappingFamilyWitness B c)).endpointIso
        pointedSpaceProjection (constantUnstraighteningFiberProjection B x)
        (intervalMappingUncurry c) (intervalMappingUncurry_one c)
        (constantDiagramTriangleLongTransport a b c H h₀₁ h₁₂ h₀₂)).precomp
          (lift (𝟙 E) (SSet.const l))) := by
  let w := unstraighteningMappingTriangleLongWitness F G J A D C H h₀₁ h₁₂ h₀₂
  let T := constantDiagramTransportWitness (constantDiagramMappingFamilyWitness B c)
  let U := constantDiagramTriangleLongTransport a b c H h₀₁ h₁₂ h₀₂
  let e := T.endpointIso pointedSpaceProjection (constantUnstraighteningFiberProjection B x)
    (intervalMappingUncurry c) (intervalMappingUncurry_one c) U
  let m := lift (A ≫ leftUnstraighteningMappingSpaceMap F G)
    (D ≫ leftUnstraighteningMappingSpaceMap G J) ≫
      relativeFunctorComposition (Over.mk q) (Over.mk (leftUnstraighteningProjection G))
        (Over.mk (leftUnstraighteningProjection J))
  let h := lift (relativeFunctorUncurry (A ≫ leftUnstraighteningMappingSpaceMap F G))
    (snd E K) ≫ relativeFunctorUncurry (D ≫ leftUnstraighteningMappingSpaceMap G J)
  have hh := unstraighteningMappingComposite_projection F G J A D
  have hc : relativeFunctorCurry h hh = m := by
    apply relativeFunctorUncurry_injective
    rw [relativeFunctorUncurry_curry]
    apply SSet.hom_ext
    intro n
    rfl
  have hs := (constantDiagramTransportWitness_map_of_uncurry
    (C ≫ leftUnstraighteningMappingSpaceMap F J)
    (constantDiagramMappingFamilyWitness B c)).symm
  have ht : m ≫ (constantUnstraighteningRelativeIso q z).hom = U.map := by
    rw [← hc]
    exact (constantDiagramTransportWitness_map hh w).symm
  have he := (constantDiagramTriangleComparison_heq_fiber a b c H h₀₁ h₁₂ h₀₂).trans
    (functorIso_curry_heq_map e).symm
  have happ := functorIso_app_heq_of_heq _ e.curry hs ht he l
  exact happ.trans (functorIso_curry_app_heq_precomp e l)

end SerrePositivity.InfinityCategories.F2
