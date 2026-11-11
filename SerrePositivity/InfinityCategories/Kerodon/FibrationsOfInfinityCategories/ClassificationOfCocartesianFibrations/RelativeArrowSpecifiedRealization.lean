module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowCoherentRealization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationSum
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallCartesianRepresentationExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallFiberCartesianExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowSmallFibers

/-!
概要：指定した両端表現を厳密に保ち相対射を coherent な区間図式に実現する。
方針：両端の和の表現を collage 上へ境界固定で延長する。
規約：分類図式と pointed space への射を同時に固定する。
使われ方：非可逆な写像空間比較の指定端点での復元。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：指定した二つの表現の間の任意の相対射は coherent な区間図式を持つ。
方針：両端の和を単射としてまとめ小さい全空間の相対延長を適用する。
規約：元の射と両端の分類図式・全空間側の射を厳密に保持する。
使われ方：coherent な非可逆変換の写像空間比較。 -/
lemma exists_relativeArrow_specified_coherent_realization_of_small_fibers {E F B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (hsmallp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hsmallq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q)
    (R₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (R₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q) :
    ∃ (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (K : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H = R₀.diagram ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ H = R₁.diagram ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ K = R₀.pointedMap ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ K = f ≫ R₁.pointedMap ∧
      K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = (Δ[1] ◁ p) ≫ H := by
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_leftFibration p q f hf
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f (𝟙 F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 F))
  have hp : IsPullback e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointMap p q) r (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair B) :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.isPullback_prismEndpointPair p q r _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollage_inl_isPullback p q f hf)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollage_inr_isPullback f q)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointMap p q) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.of_isPullback hp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := r))⟩
  let a : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointMap p q) ⟶ Arrow.mk r :=
    Arrow.homMk e (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair B) hp.w
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointMap p q)).hom := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointMap p q); infer_instance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (Arrow.mk r).hom := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r; exact hr
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers (Arrow.mk r).hom := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers r
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_hasSmallSimplexFibers p q f hf hsmallp hsmallq
  have : Mono a.right := by change Mono (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair B); infer_instance
  obtain ⟨R, hR⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.exists_smallFiber_cartesianTransportRepresentation_extension hs a hp (R₀.sum R₁)
  change R.cartesianRestrict e (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair B) hp = R₀.sum R₁ at hR
  have hd : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair B ≫ R.diagram = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc R₀.diagram R₁.diagram :=
    congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.diagram hR
  have hm : e ≫ R.pointedMap = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc R₀.pointedMap R₁.pointedMap := by
    rw [← R.cartesianRestrict_pointedMap e (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair B) hp, hR]
    exact R₀.sum_pointedMap R₁
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f (𝟙 F) ≫ R.pointedMap = R₀.pointedMap := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app hm d)
      (Sum.inl x : E.obj d ⊕ F.obj d)
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 F) ≫ R.pointedMap = R₁.pointedMap := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app hm d)
      (Sum.inr x : E.obj d ⊕ F.obj d)
  refine ⟨R.diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ R.pointedMap, ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero, h₀]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_one, Category.assoc, h₁]
  · rw [Category.assoc, R.pointedMap_projection, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ R.diagram) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_prism p q f hf)


/-- 概要：小さい全空間の指定両端の実現は次数 fiber の一般の定理に従う。
方針：全空間の小ささを次数 fiber の小ささへ渡す。
規約：従来の界面を保つ。
使われ方：小さい底上の写像空間比較。 -/
lemma exists_relativeArrow_specified_coherent_realization {E F B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (R₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (R₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q) :
    ∃ (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (K : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H = R₀.diagram ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ H = R₁.diagram ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ K = R₀.pointedMap ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ K = f ≫ R₁.pointedMap ∧
      K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = (Δ[1] ◁ p) ≫ H := by
  exact exists_relativeArrow_specified_coherent_realization_of_small_fibers p q f hf
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasSmallSimplexFibers_of_small_total p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasSmallSimplexFibers_of_small_total q) R₀ R₁

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
