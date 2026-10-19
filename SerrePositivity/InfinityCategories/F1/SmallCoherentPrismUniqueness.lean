module

public import SerrePositivity.InfinityCategories.F1.BoundaryRepresentationTransformationIso
public import SerrePositivity.InfinityCategories.F1.CoherentCollageRepresentationRecovery
public import SerrePositivity.InfinityCategories.F1.RelativeArrowCollageRepresentation
public import SerrePositivity.InfinityCategories.F1.RelativeArrowSmallFibers

/-!
概要：同じ小さい相対射を表す二つの coherent な prism は固定端点で同型。
方針：双方を同じ collage の指定境界の表現へ戻し可縮な fiber で比較する。
規約：分類図式全体と両端を保つ比較を与える。
使われ方：写像空間比較の復元の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：両端の図式の条件は両端の和の図式を決定する。
方針：直和の各成分で指定した端点の等式を使う。
規約：標的と底は任意。
使われ方：二つの表現を同じ境界 fiber へ入れる。 -/
lemma prismEndpointPair_comp_eq {B X : SSet.{u}} (F G : B ⟶ X)
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ X)
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    prismEndpointPair B ≫ H = joinEndpointDesc F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | inl x => exact congrArg (fun f : B ⟶ X ↦ f.app n x) h₀
  | inr x => exact congrArg (fun f : B ⟶ X ↦ f.app n x) h₁

/-- 概要：同じ小さい相対射の二つの pointed な prism は変換空間内で同型となる。
方針：元の両図式を指定両端の collage 表現へ戻し可縮な境界 fiber で比較する。
規約：次数 fiber の小ささのみを要求し、底と全空間は任意。
使われ方：一般の coherent な変換の復元の一意性。 -/
lemma coherentPrism_uniqueness_of_small_fibers {E F B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (hsmallp : HasSmallSimplexFibers p) (hsmallq : HasSmallSimplexFibers q)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q)
    (H H' : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = R₀.diagram)
    (h₁ : prismEndpoint 1 B ≫ H = R₁.diagram)
    (h₀' : prismEndpoint 0 B ≫ H' = R₀.diagram)
    (h₁' : prismEndpoint 1 B ≫ H' = R₁.diagram)
    (W W' : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u})
    (hw₀ : prismEndpoint 0 E ≫ W = R₀.pointedMap)
    (hw₁ : prismEndpoint 1 E ≫ W = f ≫ R₁.pointedMap)
    (hw₀' : prismEndpoint 0 E ≫ W' = R₀.pointedMap)
    (hw₁' : prismEndpoint 1 E ≫ W' = f ≫ R₁.pointedMap)
    (hwp : W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H)
    (hwp' : W' ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H') :
    Nonempty (VertexIso
      (intervalMappingVertexOfEdge (functorEdgeFromPrism H h₀ h₁))
      (intervalMappingVertexOfEdge (functorEdgeFromPrism H' h₀' h₁'))) := by
  have hr := relativeArrowCollageProjection_leftFibration p q f hf
  obtain ⟨R, hdR, hmR⟩ :=
    exists_coherentCollage_representation_recovery p q f hf R₀ R₁ H h₀ h₁ W hw₀ hw₁ hwp
  obtain ⟨T, hdT, hmT⟩ :=
    exists_coherentCollage_representation_recovery p q f hf R₀ R₁ H' h₀' h₁' W' hw₀' hw₁' hwp'
  subst H
  subst H'
  let r := relativeArrowCollageProjection f q
  have hsmall : HasSmallSimplexFibers r :=
    relativeArrowCollageProjection_hasSmallSimplexFibers p q f hf hsmallp hsmallq
  let e := joinEndpointDesc (relativeJoinInl f (𝟙 F)) (relativeJoinInr f (𝟙 F))
  have hp : IsPullback e (joinEndpointMap p q) r (prismEndpointPair B) :=
    isPullback_prismEndpointPair p q r _ _
      (relativeArrowCollage_inl_isPullback p q f hf) (relativeArrowCollage_inr_isPullback f q)
  have : LeftFibration (joinEndpointMap p q) :=
    ⟨leftFibrations.of_isPullback hp hr.mem⟩
  have hR : R.cartesianRestrict e (prismEndpointPair B) hp = R₀.sum R₁ := by
    apply (R.cartesianRestrict_eq_iff (R₀.sum R₁) e (prismEndpointPair B) hp).mpr
    constructor
    · exact prismEndpointPair_comp_eq R₀.diagram R₁.diagram R.diagram h₀ h₁
    · exact hmR.trans (R₀.sum_pointedMap R₁).symm
  have hT : T.cartesianRestrict e (prismEndpointPair B) hp = R₀.sum R₁ := by
    apply (T.cartesianRestrict_eq_iff (R₀.sum R₁) e (prismEndpointPair B) hp).mpr
    constructor
    · exact prismEndpointPair_comp_eq R₀.diagram R₁.diagram T.diagram h₀' h₁'
    · exact hmT.trans (R₀.sum_pointedMap R₁).symm
  exact ⟨smallFiberBoundaryRepresentation_transformationIso r hsmall (joinEndpointMap p q) e hp
    R₀.diagram R₁.diagram (R₀.sum R₁) rfl R T hR hT h₀ h₁ h₀' h₁'⟩

/-- 小さい全空間の場合は次数 fiber の比較に従う。 -/
lemma small_coherentPrism_uniqueness {E F B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q)
    (H H' : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = R₀.diagram)
    (h₁ : prismEndpoint 1 B ≫ H = R₁.diagram)
    (h₀' : prismEndpoint 0 B ≫ H' = R₀.diagram)
    (h₁' : prismEndpoint 1 B ≫ H' = R₁.diagram)
    (W W' : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u})
    (hw₀ : prismEndpoint 0 E ≫ W = R₀.pointedMap)
    (hw₁ : prismEndpoint 1 E ≫ W = f ≫ R₁.pointedMap)
    (hw₀' : prismEndpoint 0 E ≫ W' = R₀.pointedMap)
    (hw₁' : prismEndpoint 1 E ≫ W' = f ≫ R₁.pointedMap)
    (hwp : W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H)
    (hwp' : W' ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H') :
    Nonempty (VertexIso
      (intervalMappingVertexOfEdge (functorEdgeFromPrism H h₀ h₁))
      (intervalMappingVertexOfEdge (functorEdgeFromPrism H' h₀' h₁'))) :=
  coherentPrism_uniqueness_of_small_fibers p q f hf
    (hasSmallSimplexFibers_of_small_total p) (hasSmallSimplexFibers_of_small_total q)
    R₀ R₁ H H' h₀ h₁ h₀' h₁' W W' hw₀ hw₁ hw₀' hw₁' hwp hwp'

end SerrePositivity.InfinityCategories
