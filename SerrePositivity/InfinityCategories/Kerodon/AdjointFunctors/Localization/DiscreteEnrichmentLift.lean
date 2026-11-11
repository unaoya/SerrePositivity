module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentUnderlying

/-!
# 通常の underlying 圏への関手の元の離散豊穣化

概要：通常の関手の各射の一定単体写像を元の離散 Hom からの単体写像へ束ねる。
方針：元の自然性と通常の関手の単位・合成保存を使う。
規約：元の対象と元の全射の像を保持する。
使われ方：非指定自由部分からの豊穣関手の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type uD} [EnrichedCategory SSet.{v} D]
  (K : C ⥤ ForgetEnrichment SSet.{v} D)

def liftMap (X Y : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.hom X Y ⟶
    ForgetEnrichment.to SSet.{v} (K.obj X) ⟶[SSet.{v}] ForgetEnrichment.to SSet.{v} (K.obj Y) where
  app n := ↾fun f => (ForgetEnrichment.homTo SSet.{v} (K.map f)).app n PUnit.unit
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact congrArg (fun k => k PUnit.unit)
      ((ForgetEnrichment.homTo SSet.{v} (K.map f)).naturality θ)

lemma liftMap_point {X Y : C} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point f ≫ liftMap K X Y = ForgetEnrichment.homTo SSet.{v} (K.map f) := by
  ext n p
  rfl

def liftFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
    EnrichedFunctor SSet.{v} C D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
  exact
    { obj := fun X => ForgetEnrichment.to SSet.{v} (K.obj X)
      map := liftMap K
      map_id := fun X => by
        ext n p
        have hi := congrArg (fun f => (ForgetEnrichment.homTo SSet.{v} f).app n PUnit.unit)
          (K.map_id X)
        exact hi.trans (congrArg (fun f => f.app n PUnit.unit)
          (ForgetEnrichment.homTo_id SSet.{v} (K.obj X)))
      map_comp := fun X Y Z => by
        ext n p
        have hc := congrArg (fun f => (ForgetEnrichment.homTo SSet.{v} f).app n PUnit.unit)
          (K.map_comp p.1 p.2)
        exact hc.trans (congrArg (fun f => f.app n PUnit.unit)
          (ForgetEnrichment.homTo_comp SSet.{v} (K.map p.1) (K.map p.2))) }

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift
