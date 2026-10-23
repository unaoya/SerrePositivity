module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.RelativeArrowCoherentRealization
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationSum
public import SerrePositivity.InfinityCategories.F1.Universe.SmallCartesianRepresentationExtension
public import SerrePositivity.InfinityCategories.F1.Universe.SmallFiberCartesianExtension
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.RelativeArrowSmallFibers

/-!
概要：指定した両端表現を厳密に保ち相対射を coherent な区間図式に実現する。
方針：両端の和の表現を collage 上へ境界固定で延長する。
規約：分類図式と pointed space への射を同時に固定する。
使われ方：非可逆な写像空間比較の指定端点での復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した二つの表現の間の任意の相対射は coherent な区間図式を持つ。
方針：両端の和を単射としてまとめ小さい全空間の相対延長を適用する。
規約：元の射と両端の分類図式・全空間側の射を厳密に保持する。
使われ方：coherent な非可逆変換の写像空間比較。 -/
lemma exists_relativeArrow_specified_coherent_realization_of_small_fibers {E F B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (hsmallp : HasSmallSimplexFibers p) (hsmallq : HasSmallSimplexFibers q)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q) :
    ∃ (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
      (K : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u}),
      prismEndpoint 0 B ≫ H = R₀.diagram ∧
      prismEndpoint 1 B ≫ H = R₁.diagram ∧
      prismEndpoint 0 E ≫ K = R₀.pointedMap ∧
      prismEndpoint 1 E ≫ K = f ≫ R₁.pointedMap ∧
      K ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H := by
  let r := relativeArrowCollageProjection f q
  have hr : LeftFibration r := relativeArrowCollageProjection_leftFibration p q f hf
  let e := joinEndpointDesc (relativeJoinInl f (𝟙 F)) (relativeJoinInr f (𝟙 F))
  have hp : IsPullback e (joinEndpointMap p q) r (prismEndpointPair B) :=
    isPullback_prismEndpointPair p q r _ _
      (relativeArrowCollage_inl_isPullback p q f hf)
      (relativeArrowCollage_inr_isPullback f q)
  have : LeftFibration (joinEndpointMap p q) :=
    ⟨leftFibrations.of_isPullback hp (LeftFibration.mem (p := r))⟩
  let a : Arrow.mk (joinEndpointMap p q) ⟶ Arrow.mk r :=
    Arrow.homMk e (prismEndpointPair B) hp.w
  have : LeftFibration (Arrow.mk (joinEndpointMap p q)).hom := by
    change LeftFibration (joinEndpointMap p q); infer_instance
  have : LeftFibration (Arrow.mk r).hom := by change LeftFibration r; exact hr
  have hs : HasSmallSimplexFibers (Arrow.mk r).hom := by
    change HasSmallSimplexFibers r
    exact relativeArrowCollageProjection_hasSmallSimplexFibers p q f hf hsmallp hsmallq
  have : Mono a.right := by change Mono (prismEndpointPair B); infer_instance
  obtain ⟨R, hR⟩ := exists_smallFiber_cartesianTransportRepresentation_extension hs a hp (R₀.sum R₁)
  change R.cartesianRestrict e (prismEndpointPair B) hp = R₀.sum R₁ at hR
  have hd : prismEndpointPair B ≫ R.diagram = joinEndpointDesc R₀.diagram R₁.diagram :=
    congrArg LeftTransportRepresentation.diagram hR
  have hm : e ≫ R.pointedMap = joinEndpointDesc R₀.pointedMap R₁.pointedMap := by
    rw [← R.cartesianRestrict_pointedMap e (prismEndpointPair B) hp, hR]
    exact R₀.sum_pointedMap R₁
  have h₀ : relativeJoinInl f (𝟙 F) ≫ R.pointedMap = R₀.pointedMap := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app hm d)
      (Sum.inl x : E.obj d ⊕ F.obj d)
  have h₁ : relativeJoinInr f (𝟙 F) ≫ R.pointedMap = R₁.pointedMap := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app hm d)
      (Sum.inr x : E.obj d ⊕ F.obj d)
  refine ⟨R.diagram, relativeJoinPrism f ≫ R.pointedMap, ?_, ?_, ?_, ?_, ?_⟩
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app hd d)
      (Sum.inl x : B.obj d ⊕ B.obj d)
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app hd d)
      (Sum.inr x : B.obj d ⊕ B.obj d)
  · rw [← Category.assoc, relativeJoinPrism_zero, h₀]
  · rw [← Category.assoc, relativeJoinPrism_one, Category.assoc, h₁]
  · rw [Category.assoc, R.pointedMap_projection, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ R.diagram) (relativeArrowCollageProjection_prism p q f hf)


/-- 概要：小さい全空間の指定両端の実現は次数 fiber の一般の定理に従う。
方針：全空間の小ささを次数 fiber の小ささへ渡す。
規約：従来の界面を保つ。
使われ方：小さい底上の写像空間比較。 -/
lemma exists_relativeArrow_specified_coherent_realization {E F B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q) :
    ∃ (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
      (K : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u}),
      prismEndpoint 0 B ≫ H = R₀.diagram ∧
      prismEndpoint 1 B ≫ H = R₁.diagram ∧
      prismEndpoint 0 E ≫ K = R₀.pointedMap ∧
      prismEndpoint 1 E ≫ K = f ≫ R₁.pointedMap ∧
      K ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H := by
  exact exists_relativeArrow_specified_coherent_realization_of_small_fibers p q f hf
    (hasSmallSimplexFibers_of_small_total p) (hasSmallSimplexFibers_of_small_total q) R₀ R₁

end SerrePositivity.InfinityCategories
