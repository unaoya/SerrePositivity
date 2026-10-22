module

public import SerrePositivity.InfinityCategories.F2.UnstraighteningSourceComparisonPresentation
public import SerrePositivity.InfinityCategories.F2.UnstraighteningMappingIdentityData
public import SerrePositivity.InfinityCategories.F2.UnstraighteningFamilyEndpointBase
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionCurryEndpointEquality

/-!
概要：始域恒等射付きの指定比較を、同じ普遍証拠と指定証拠の終点比較へ戻す。
方針：普遍 prism と相対 uncurry の恒等始域表示を厳密に揃える。
規約：指定された二証拠を保持。使われ方：元の三角形比較の fiber 表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (t : K ⟶ leftUnstraighteningTransformationSpace F G)
local notation "E" => leftUnstraightening F
local notation "p" => leftUnstraighteningProjection F
local notation "d" => ((Δ[1] ◁ p) ▷ K) ≫
  functorParameterizedPrism (intervalMappingUncurry t)
local notation "v" => fst E K ≫ pullback.fst pointedSpaceProjection F
local notation "g" => relativeFunctorUncurry (t ≫ leftUnstraighteningMappingSpaceMap F G)
local notation "w" => unstraighteningMappingFamilyWitness F G t
local notation "hv" => unstraighteningMappingFamilyWitness_initial_base F G t
local notation "hj" => unstraighteningMappingFamilyWitness_final_base F G t

/-- 元の指定比較を、同じ実普遍証拠と指定証拠の curry 比較として保持する。 -/
lemma unstraighteningSourceComparisonIso_heq_actualWitness
    (f : E ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = fst E K ≫ p)
    (W : UnstraighteningFamilyWitness F G t f) :
    HEq (unstraighteningSourceFamilyComparisonIso F G p (𝟙 E) (Category.id_comp _)
      t f hf W.prism W.source W.target W.projection)
      (relativeFunctorExtensionEndpoint_curryIso pointedSpaceProjection d
        (prismEndpoint 0 E ▷ K)
        (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K)
        v hv (prismEndpoint 1 E ▷ K) G p hj
        (UnstraighteningFamilyWitness.prism w) W.prism
        (UnstraighteningFamilyWitness.projection w) W.projection
        (UnstraighteningFamilyWitness.source w) W.source g f
        (relativeFunctorUncurry_projection _) hf
        (UnstraighteningFamilyWitness.target w) W.target) := by
  have hz : (((Δ[1] ◁ 𝟙 E) ⊗ₘ t) ≫
      leftUnstraighteningTransformationFamilyLift F G) ≫ pointedSpaceProjection = d := by
    rw [unstraighteningMappingFamilyWitness_identity_prism]
    exact UnstraighteningFamilyWitness.projection w
  have hz₀ : (prismEndpoint 0 E ▷ K) ≫ (((Δ[1] ◁ 𝟙 E) ⊗ₘ t) ≫
      leftUnstraighteningTransformationFamilyLift F G) =
      fst E K ≫ 𝟙 E ≫ pullback.fst pointedSpaceProjection F := by
    rw [unstraighteningMappingFamilyWitness_identity_prism, Category.id_comp]
    exact UnstraighteningFamilyWitness.source w
  have hg : ((𝟙 E ⊗ₘ t) ≫ relativeFunctorUncurry
      (leftUnstraighteningMappingSpaceMap F G)) ≫ leftUnstraighteningProjection G =
      fst E K ≫ p := by
    rw [unstraighteningMappingFamilyWitness_identity_action]
    exact relativeFunctorUncurry_projection _
  have hz₁ : (prismEndpoint 1 E ▷ K) ≫ (((Δ[1] ◁ 𝟙 E) ⊗ₘ t) ≫
      leftUnstraighteningTransformationFamilyLift F G) =
      ((𝟙 E ⊗ₘ t) ≫ relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G)) ≫
        pullback.fst pointedSpaceProjection G := by
    rw [unstraighteningMappingFamilyWitness_identity_prism,
      unstraighteningMappingFamilyWitness_identity_action]
    exact UnstraighteningFamilyWitness.target w
  have h := unstraighteningSourceComparisonIso_heq_endpoint F G p (𝟙 E) (Category.id_comp _)
    t f hf W.prism W.source W.target W.projection hz hz₀ hg hz₁
    (by simpa only [Category.id_comp] using hv) hj
  simp only [unstraighteningMappingFamilyWitness_identity_prism, Category.id_comp] at h
  refine h.trans ?_
  exact relativeExtensionEndpoint_curryIso_heq_of_sourceEq pointedSpaceProjection d
    (prismEndpoint 0 E ▷ K)
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K)
    v hv (prismEndpoint 1 E ▷ K) G p hj
    (UnstraighteningFamilyWitness.prism w) W.prism
    (UnstraighteningFamilyWitness.projection w) W.projection
    (UnstraighteningFamilyWitness.source w) W.source _ g f hg
    (relativeFunctorUncurry_projection _) hf
    (by simpa only [unstraighteningMappingFamilyWitness_identity_prism] using hz₁)
    (UnstraighteningFamilyWitness.target w) W.target
    (unstraighteningMappingFamilyWitness_identity_action F G t)

end SerrePositivity.InfinityCategories.F2
