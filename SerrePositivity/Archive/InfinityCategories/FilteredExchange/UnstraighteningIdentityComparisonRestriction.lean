module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningIdentityPrismData
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningSourceComparisonRestriction

/-!
概要：恒等始域での実際の unstraightening 比較の各点成分を延長空間へ制限する。
方針：同じ普遍 prism の六条件を既存の始域付き成分比較へ適用する。
規約：指定 prism と実際の指定同型を保持。使われ方：全三角形比較の fiber 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K C : SSet.{u + 1}} [Quasicategory K]
  (F G : B ⟶ SpaceInfinity.{u}) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
  (f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G)
  (hf : f ≫ leftUnstraighteningProjection G =
    fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
  (W : (Δ[1] ⊗ leftUnstraightening F) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hw₀ : (prismEndpoint 0 (leftUnstraightening F) ▷ K) ≫ W =
    fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F)
  (hw₁ : (prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ W =
    f ≫ pullback.fst pointedSpaceProjection G)
  (hwp : W ≫ pointedSpaceProjection = ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
    functorParameterizedPrism (intervalMappingUncurry t))
  (l : K _⦋0⦌) (s₀ : C ⟶ leftUnstraightening F)
local notation "A" => leftUnstraightening F
local notation "Z" => ((Δ[1] ◁ 𝟙 A) ⊗ₘ t) ≫ leftUnstraighteningTransformationFamilyLift F G
local notation "d" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
  functorParameterizedPrism (intervalMappingUncurry t)
local notation "v" => fst A K ≫ 𝟙 A ≫ pullback.fst pointedSpaceProjection F
local notation "hv" => unstraighteningIdentityPrism_initial F G t
local notation "s" => s₀ ≫ lift (𝟙 A) (SSet.const l)
local notation "r" => prismExtensionRestriction pointedSpaceProjection d v hv s

/-- 元の二つの実 prism を制限した後の延長空間の指定終点比較。 -/
def unstraighteningIdentityRestrictedEndpointIso :=
  VertexIso.map
    ((relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection
      (prismParameterRestriction s ≫ d) (prismEndpoint 0 C)
      (prismEndpoint_zero_leftAnodyne C) (s ≫ v)
      (by rw [Category.assoc, hv]; rfl)).vertexIso
      ((r).app _ (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
        (prismEndpoint 0 A ▷ K) v hv
        ⟨Z, unstraighteningIdentityPrism_projection F G t,
          unstraighteningIdentityPrism_source F G t⟩))
      ((r).app _ (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
        (prismEndpoint 0 A ▷ K) v hv ⟨W, hwp, hw₀⟩)))
    (relativeFunctorExtensionEndpoint pointedSpaceProjection (prismParameterRestriction s ≫ d)
      (prismEndpoint 0 C) (s ≫ v) (by rw [Category.assoc, hv]; rfl)
      (prismEndpoint 1 C) G (s ≫ (fst A K ≫ leftUnstraighteningProjection F))
      (prismExtensionPullbackRestriction_endpoint d s G (fst A K ≫ leftUnstraighteningProjection F)
        (unstraighteningIdentityPrism_endpoint F G t)))

/-- 実際の恒等始域の比較成分は同じ二 prism の制限後の指定終点比較。 -/
lemma unstraighteningIdentityComparisonIso_app_pre :
    HEq
      (VertexIso.map
        ((unstraighteningSourceFamilyComparisonIso F G (leftUnstraighteningProjection F)
          (𝟙 A) (Category.id_comp _) t f hf W hw₀ hw₁ hwp).app l)
        (relativeFunctorPre (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) s₀))
      (unstraighteningIdentityRestrictedEndpointIso F G t W hw₀ hwp l s₀) :=
  unstraighteningSourceComparisonIso_app_pre F G (leftUnstraighteningProjection F)
    (𝟙 A) (Category.id_comp _) t f hf W hw₀ hw₁ hwp
    (unstraighteningIdentityPrism_projection F G t)
    (unstraighteningIdentityPrism_source F G t)
    (unstraighteningIdentityFamily_projection F G t)
    (unstraighteningIdentityPrism_target F G t) hv
    (unstraighteningIdentityPrism_endpoint F G t) l s₀

end SerrePositivity.InfinityCategories.F2
