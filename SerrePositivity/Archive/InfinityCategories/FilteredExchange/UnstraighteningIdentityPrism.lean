module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningMappingTrianglePrism

/-!
概要：恒等始域での始域付き比較が、全三角形の辺に使う同じ普遍 prism を持つ。
方針：恒等射とのテンソルとパラメータ制限を全単体で照合する。
規約：元の普遍的な持ち上げを保持。使われ方：実際の三角形比較の fiber 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (t : K ⟶ leftUnstraighteningTransformationSpace F G)

/-- 恒等始域からの普遍 prism は元の族に制限した同じ普遍的な持ち上げ。 -/
lemma unstraighteningIdentityPrism_eq :
    ((Δ[1] ◁ 𝟙 (leftUnstraightening F)) ⊗ₘ t) ≫
        leftUnstraighteningTransformationFamilyLift F G =
      (unstraighteningMappingFamilyWitness F G t).prism := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 恒等始域からの終点の族は元の比較射の同じ uncurry。 -/
lemma unstraighteningIdentityFamily_eq :
    (𝟙 (leftUnstraightening F) ⊗ₘ t) ≫
        relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) =
      relativeFunctorUncurry (t ≫ leftUnstraighteningMappingSpaceMap F G) := by
  rw [relativeFunctorUncurry_naturality]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
