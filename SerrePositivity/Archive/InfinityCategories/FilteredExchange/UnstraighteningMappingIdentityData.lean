module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningMappingTrianglePrism

/-!
概要：始域恒等射付きの普遍証拠を、同じ実 prism と実作用へ同定する。
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

/-- 始域恒等射の普遍 prism は同じ写像空間作用の元の証拠の prism。 -/
lemma unstraighteningMappingFamilyWitness_identity_prism :
    ((Δ[1] ◁ 𝟙 E) ⊗ₘ t) ≫ leftUnstraighteningTransformationFamilyLift F G =
      UnstraighteningFamilyWitness.prism w := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 始域恒等射での実作用は、元の族の相対 uncurry そのもの。 -/
lemma unstraighteningMappingFamilyWitness_identity_action :
    (𝟙 E ⊗ₘ t) ≫ relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) = g := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
