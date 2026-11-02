module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningRestrictedVertex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeUncurryPointVertices

/-!
概要：制限後の普遍 prism の終点の実頂点を元の指定射の始域制限と照合する。
方針：恒等始域の族を同じ uncurry に戻し、元の定値変換の一点評価を使う。
規約：普遍 prism を選び直さない。使われ方：局所延長比較の始点の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K C : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (z : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (k : K _⦋0⦌) (s : C ⟶ leftUnstraightening F)
local notation "t" => (SSet.const z : K ⟶ leftUnstraighteningTransformationSpace F G)
local notation "Z" => ((Δ[1] ◁ 𝟙 (leftUnstraightening F)) ⊗ₘ t) ≫
  leftUnstraighteningTransformationFamilyLift F G

/-- 同じ普遍 prism の制限後の終点は元の変換の実際の全空間射の制限。 -/
lemma restrictedUniversalEndpoint_vertex :
    unstraighteningRestrictedEndpointVertex F G t Z
      (unstraighteningIdentityPrism_source F G t)
      (unstraighteningIdentityPrism_projection F G t) k s =
    relativeFunctorVertex (leftUnstraighteningProjection G) (s ≫ leftUnstraighteningProjection F)
      (s ≫ (leftUnstraighteningMappingVertexMap F G z).val)
      (by rw [Category.assoc, (leftUnstraighteningMappingVertexMap F G z).property]) := by
  apply unstraighteningRestrictedEndpointVertex_point F G t Z
    (unstraighteningIdentityPrism_source F G t)
    (unstraighteningIdentityPrism_projection F G t) k s
    ((𝟙 (leftUnstraightening F) ⊗ₘ t) ≫
      relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G))
    (unstraighteningIdentityFamily_projection F G t)
    (unstraighteningIdentityPrism_target F G t)
    (leftUnstraighteningMappingVertexMap F G z).val
    (leftUnstraighteningMappingVertexMap F G z).property
  rw [unstraighteningIdentityFamily_eq]
  exact unstraighteningUncurryConst_point F G z k

end SerrePositivity.InfinityCategories.F2
