module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawUnitInvariance
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingFibers
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexEquivalenceLifting

/-!
概要：随伴単位の全部分空間の包含と両写像空間への射影は Kan fibration。
方針：指定単位条件の同型不変性で前合成同値を持ち上げ、core 同型と射影を合成する。
規約：モデル構造の instance を仮定せず、具体的な全ホーンの持ち上げ性を使う。
使われ方：両射影の QCat 同値性に必要な辺の持ち上げ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：Kan 第二因子を持つ直積の第一射影は全ホーンを持ち上げる。
方針：第二成分のホーンを充填し、指定された第一成分と組にする。
規約：第一因子の充填性は要求しない。
使われ方：随伴単位の底の両射影の Kan fibration 性。 -/
lemma kanProductFst_fibration (X Y : SSet.{u}) [KanComplex Y] : Fibration (fst X Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n i
  constructor
  intro a b sq
  obtain ⟨G, hG⟩ := KanComplex.hornFilling (a ≫ snd X Y)
  refine CommSq.HasLift.mk' { l := lift b G, fac_left := ?_, fac_right := lift_fst _ _ }
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst]
    exact sq.w.symm
  · rw [Category.assoc, lift_snd]
    exact hG.symm

/-- 概要：Kan 第一因子を持つ直積の第二射影は全ホーンを持ち上げる。
方針：第一成分のホーンを充填し、指定された第二成分と組にする。
規約：第二因子の充填性は要求しない。
使われ方：随伴単位の底の両射影の Kan fibration 性。 -/
lemma kanProductSnd_fibration (X Y : SSet.{u}) [KanComplex X] : Fibration (snd X Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n i
  constructor
  intro a b sq
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (a ≫ fst X Y)
  refine CommSq.HasLift.mk' { l := lift F b, fac_left := ?_, fac_right := lift_snd _ _ }
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst]
    exact hF.symm
  · rw [Category.assoc, lift_snd]
    exact sq.w.symm

/-- 概要：指定単位の随伴条件の全部分空間の包含は全ホーンを持ち上げる。
方針：両関手が動く同型不変性で前合成同値を持ち上げ、Kan 間の fibration 判定を使う。
規約：同値の存在や選択の整合性を追加仮定にしない。
使われ方：元の随伴単位の両射影の Kan fibration 性。 -/
lemma adjointUnitFullSpace_fibration (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D)
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v))).ι := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.kanEquivalenceLifting_fullSubcomplexOnVertices_ι _ (fun i ↦
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitCondition_of_vertexIso i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitCondition_of_vertexIso i.symm⟩)

/-- 概要：随伴単位の core から元の実単位の母空間への包含は Kan fibration。
方針：core の厳密同型と、指定単位条件の全部分空間の包含を合成する。
規約：元の単位の高次単体を保つ。
使われ方：両射影の全ホーンの持ち上げ。 -/
instance adjointUnitUnderlying_fibration (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitUnderlying C D) := by
  change Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitCoreIso C D).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D)
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v))).ι)
  have := adjointUnitFullSpace_fibration C D
  infer_instance

/-- 概要：元の左写像空間への随伴単位の射影は Kan fibration。
方針：随伴単位の包含、元の実単位の底射影、Kan 直積の第一射影を合成する。
規約：元の e1 の写像空間への射の全ホーン持ち上げ性。
使われ方：左射影の同値性に必要な相対充填性。 -/
instance adjointUnitLeft_fibration (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitLeft C D) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawAdjointUnitSpace_projection_fibration C D
  have := kanProductFst_fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitLeft
  infer_instance

/-- 概要：元の右写像空間への随伴単位の射影は Kan fibration。
方針：随伴単位の包含、元の実単位の底射影、Kan 直積の第二射影を合成する。
規約：元の e1 の写像空間への射の全ホーン持ち上げ性。
使われ方：右ファイバーの可縮性から右射影の同値性を得る。 -/
instance adjointUnitRight_fibration (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight C D) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawAdjointUnitSpace_projection_fibration C D
  have := kanProductSnd_fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitRight
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
