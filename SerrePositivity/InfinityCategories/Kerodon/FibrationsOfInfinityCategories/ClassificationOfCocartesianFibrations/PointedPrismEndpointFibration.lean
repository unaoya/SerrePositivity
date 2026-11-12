module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedPrismEndpointLifting

/-!
概要：始点も動く全 pointed-space lift の同時端点制限は Kan fibration。
方針：区間写像空間のホーンを充填し、区間境界の相対内部 Hom を持ち上げる。
規約：始点写像を同値に制限する前の空間全体で証明する。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の中間空間の同時端点制限。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
  HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：全 pointed-space lift の同時端点制限は left fibration。
方針：底の区間の Kan 性と境界の相対内部 Hom の left fibration 性を使う。
規約：係数 K の充填性と始点写像の同値性は要求しない。
使われ方：同時端点制限の全ホーン充填の左ホーン部分。 -/
instance pointedPrismLiftEndpoints_leftFibration (K : SSet.{u + 1})
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoints K s t) where
  mem := by
    intro T U i hi
    cases hi with
    | @intro n k hk =>
      have : Mono ((boundary 1).ι ▷ K) := by
        rw [NatTrans.mono_iff_mono_app]
        intro n
        rw [mono_iff_injective]
        intro x y h
        change (x.1.val, x.2) = (y.1.val, y.2) at h
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst h
        · exact congrArg (fun z : (Δ[1] : SSet.{u + 1}).obj n × K.obj n ↦ z.2) h
      let r := Functor.PullbackObjObj.ofHasPullback internalHom
        ((boundary 1).ι ▷ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r.π := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ _ _ r
      have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := r.π) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro k hk)
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.hasLiftingProperty_pointedPrismLiftEndpoints s t _ r
      intro a
      obtain ⟨q, hq⟩ := KanComplex.hornFilling a
      exact ⟨q, hq.symm⟩

/-- 概要：全 pointed-space lift の同時端点制限は Kan fibration。
方針：始域と標的の Kan 性から left fibration の最後のホーンも充填する。
規約：Fibration はホーンの持ち上げ性としてのみ用いる。
使われ方：始点同値への制限後に fiber ごとの同値性を使うための相対充填。 -/
lemma pointedPrismLiftEndpoints_fibration (K : SSet.{u + 1})
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoints K s t) := by
  let : KanComplex ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) ⊗
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismParameterProduct_kanComplex _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
