module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningIdentityComparisonRestriction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PrismRestrictedEndpointVertex

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
variable {B K C : SSet.{u + 1}}
  (F G : B ⟶ SpaceInfinity.{u}) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
  (W : (Δ[1] ⊗ leftUnstraightening F) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hw₀ : (prismEndpoint 0 (leftUnstraightening F) ▷ K) ≫ W =
    fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F)
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

/-- 元の実 prism を制限した後の終点の実頂点。 -/
def unstraighteningRestrictedEndpointVertex :
    (relativeFunctorSpace (leftUnstraighteningProjection G)
      (s₀ ≫ leftUnstraighteningProjection F)) _⦋0⦌ :=
  (relativeFunctorExtensionEndpoint pointedSpaceProjection (prismParameterRestriction s ≫ d)
    (prismEndpoint 0 C) (s ≫ v) (by rw [Category.assoc, hv]; rfl)
    (prismEndpoint 1 C) G (s ≫ (fst A K ≫ leftUnstraighteningProjection F))
    (prismExtensionPullbackRestriction_endpoint d s G (fst A K ≫ leftUnstraighteningProjection F)
      (unstraighteningIdentityPrism_endpoint F G t))).app _
    ((r).app _ (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
      (prismEndpoint 0 A ▷ K) v hv ⟨W, hwp, hw₀⟩))

/-- 制限後の実終点頂点は、元の底上の終点の族を同じ点と始域で制限した相対頂点。 -/
lemma unstraighteningRestrictedEndpointVertex_eq
    (f : A ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = fst A K ≫ leftUnstraighteningProjection F)
    (hw₁ : (prismEndpoint 1 A ▷ K) ≫ W = f ≫ pullback.fst pointedSpaceProjection G) :
    unstraighteningRestrictedEndpointVertex F G t W hw₀ hwp l s₀ =
      relativeFunctorVertex (leftUnstraighteningProjection G) (s₀ ≫ leftUnstraighteningProjection F)
        (s ≫ f) (by rw [Category.assoc, hf]; rfl) := by
  exact prismRestrictedEndpoint_vertex pointedSpaceProjection d v hv s G
    (fst A K ≫ leftUnstraighteningProjection F) (unstraighteningIdentityPrism_endpoint F G t)
    W hwp hw₀ f hf hw₁

/-- 元の終点の族の指定点での値を保ったまま局所終点の実頂点を照合する。 -/
lemma unstraighteningRestrictedEndpointVertex_point
    (f : A ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = fst A K ≫ leftUnstraighteningProjection F)
    (hw₁ : (prismEndpoint 1 A ▷ K) ≫ W = f ≫ pullback.fst pointedSpaceProjection G)
    (f₀ : A ⟶ leftUnstraightening G)
    (hf₀ : f₀ ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (hpoint : lift (𝟙 A) (SSet.const l) ≫ f = f₀) :
    unstraighteningRestrictedEndpointVertex F G t W hw₀ hwp l s₀ =
      relativeFunctorVertex (leftUnstraighteningProjection G) (s₀ ≫ leftUnstraighteningProjection F)
        (s₀ ≫ f₀) (by rw [Category.assoc, hf₀]) := by
  refine (unstraighteningRestrictedEndpointVertex_eq F G t W hw₀ hwp l s₀ f hf hw₁).trans ?_
  apply Subtype.ext
  apply congrArg functorVertex
  exact (Category.assoc _ _ _).trans (congrArg (fun k => s₀ ≫ k) hpoint)

end SerrePositivity.InfinityCategories.F2
