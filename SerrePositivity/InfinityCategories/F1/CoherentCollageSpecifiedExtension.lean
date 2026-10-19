module

public import SerrePositivity.InfinityCategories.F1.CoherentCollagePointedExtension
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorEssentialBoundaryExtension
public import SerrePositivity.InfinityCategories.F1.PrismEndpointPairPullback
public import SerrePositivity.InfinityCategories.F1.LeftTransportRepresentation

/-!
概要：coherent な変換から collage へ戻す pointed な相対射の両端を厳密に固定する。
方針：写像円柱の両端の和を共通境界として単射境界固定の延長を適用する。
規約：元の coherent な分類図式を変更しない。
使われ方：指定両端の collage 表現による写像空間比較の左逆の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：元の始域と終域の和を写像円柱の両端へ入れる。
方針：零端の prism と終域の pushout への包含を直和からまとめる。
規約：左右は元の始域と終域の順。
使われ方：coherent な変換の指定両端。 -/
def relativeArrowCylinderBoundary {E F : SSet.{u}} (f : E ⟶ F) :
    joinEndpointDiagram E F ⟶ pushout (prismEndpoint 1 E) f :=
  joinEndpointDesc (prismEndpoint 0 E ≫ pushout.inl (prismEndpoint 1 E) f)
    (pushout.inr (prismEndpoint 1 E) f)

/-- 概要：写像円柱の両端の和は collage への比較後に元の両端の包含。
方針：直和の二成分で prism の零端と終域包含を計算する。
規約：厳密な射の一致。
使われ方：境界の単射性と指定値を比較する。 -/
lemma relativeArrowCylinderBoundary_comparison {E F : SSet.{u}} (f : E ⟶ F) :
    relativeArrowCylinderBoundary f ≫ relativeJoinCylinderComparison f =
      joinEndpointDesc (relativeJoinInl f (𝟙 F)) (relativeJoinInr f (𝟙 F)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | inl x =>
    have h : prismEndpoint 0 E ≫ (pushout.inl (prismEndpoint 1 E) f ≫
        relativeJoinCylinderComparison f) = relativeJoinInl f (𝟙 F) := by
      rw [relativeJoinCylinderComparison_inl, relativeJoinPrism_zero]
    exact ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app h n) x
  | inr x =>
    exact ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (relativeJoinCylinderComparison_inr f) n) x

/-- 概要：底上の射の写像円柱の共通境界は collage 上で単射。
方針：両端の和の pullback に単射性を移す。
規約：元の射 f 自体の単射性は不要。
使われ方：前合成同値に沿う延長の両端固定。 -/
lemma relativeArrowCylinderBoundary_comparison_mono {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) :
    Mono (relativeArrowCylinderBoundary f ≫ relativeJoinCylinderComparison f) := by
  rw [relativeArrowCylinderBoundary_comparison]
  exact (isPullback_prismEndpointPair p q (relativeArrowCollageProjection f q) _ _
    (relativeArrowCollage_inl_isPullback p q f hf)
    (relativeArrowCollage_inr_isPullback f q)).mono_fst_of_mono

/-- 概要：coherent な変換の collage への pointed な延長は両端を厳密に保つ。
方針：共通の単射境界を固定して写像円柱比較に沿う相対延長を行う。
規約：指定した H は変更せず、全空間の小ささも要求しない。
使われ方：与えられた変換を指定両端の実際の collage 表現へ戻す。 -/
lemma exists_coherentCollage_pointed_extension_with_endpoints {E F B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q)
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₁ : prismEndpoint 1 B ≫ H = R₁.diagram)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u})
    (hw₀ : prismEndpoint 0 E ≫ W = R₀.pointedMap)
    (hw₁ : prismEndpoint 1 E ≫ W = f ≫ R₁.pointedMap)
    (hwp : W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H) :
    ∃ (L : relativeJoin f (𝟙 F) ⟶ PointedSpaceInfinity.{u})
      (_hL : L ≫ pointedSpaceProjection = relativeArrowCollageProjection f q ≫ H),
      joinEndpointDesc (relativeJoinInl f (𝟙 F)) (relativeJoinInr f (𝟙 F)) ≫ L =
        joinEndpointDesc R₀.pointedMap R₁.pointedMap := by
  have hQ : R₁.pointedMap ≫ pointedSpaceProjection = q ≫ (prismEndpoint 1 B ≫ H) := by
    rw [h₁]
    exact R₁.pointedMap_projection
  let V := relativeArrowCylinderPointedMap f W R₁.pointedMap hw₁
  have hV := relativeArrowCylinderPointedMap_projection p q f hf H W R₁.pointedMap hw₁ hwp hQ
  have := relativeArrowCylinderBoundary_comparison_mono p q f hf
  obtain ⟨L, hL, heq, _⟩ := exists_relativeFunctorEssential_boundary_extension
    pointedSpaceProjection (relativeArrowCollageProjection f q ≫ H)
    (relativeJoinCylinderComparison f)
    (isPrecompositionEquivalence_relativeJoinCylinderComparison f)
    (relativeArrowCylinderBoundary f) V hV
  refine ⟨L, hL, ?_⟩
  rw [relativeArrowCylinderBoundary_comparison] at heq
  refine heq.trans ?_
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | inl x =>
    have h : prismEndpoint 0 E ≫ (pushout.inl (prismEndpoint 1 E) f ≫ V) =
        R₀.pointedMap := by
      rw [show pushout.inl (prismEndpoint 1 E) f ≫ V = W from pushout.inl_desc _ _ _, hw₀]
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app h n) x
  | inr x =>
    have h : pushout.inr (prismEndpoint 1 E) f ≫ V = R₁.pointedMap := pushout.inr_desc _ _ _
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app h n) x

end SerrePositivity.InfinityCategories
