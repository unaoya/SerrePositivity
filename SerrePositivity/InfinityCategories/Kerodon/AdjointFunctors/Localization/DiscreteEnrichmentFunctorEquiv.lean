module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift

/-!
# 元の離散豊穣圏からの関手と通常の underlying 圏への関手の同値

概要：元の射の一定単体による移送と離散豊穣化は互いに逆である。
方針：元の対象・全射と一定単体上の外延性を使う。
規約：元の対象写像と各 Hom の単体写像を保持する。
使われ方：非指定自由部分からの豊穣関手を生成矢の像へ移す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentFunctorEquiv
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type uD} [EnrichedCategory SSet.{v} D]

lemma ordinary_lift (K : C ⥤ ForgetEnrichment SSet.{v} D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftFunctor K) = K := by
  apply CategoryTheory.Functor.hext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftFunctor K)) (G := K) (fun _ => rfl)
  intro X Y f
  change HEq (ForgetEnrichment.homOf SSet.{v} (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap K X Y)) (K.map f)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap_point]
  rfl

lemma lift_ordinary :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
    ∀ F : EnrichedFunctor SSet.{v} C D, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor F) = F := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
  intro F
  apply EnrichedFunctor.ext SSet.{v} (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor F)) (G := F) (fun _ => rfl)
  intro X Y
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor F) X Y = F.map X Y := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap_point (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor F) f
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor F) X Y ≫ 𝟙 (F.obj X ⟶[SSet.{v}] F.obj Y) = F.map X Y
  exact (Category.comp_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor F) X Y)).trans he

def functorEquiv :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
    EnrichedFunctor SSet.{v} C D ≃ (C ⥤ ForgetEnrichment SSet.{v} D) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
  exact
    { toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ordinaryFunctor
      invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftFunctor
      left_inv := lift_ordinary
      right_inv := ordinary_lift }

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentFunctorEquiv
