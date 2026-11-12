module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment

/-!
# 元の離散豊穣圏の射と通常の underlying 圏への比較

概要：元の射を同じ一定単体写像へ送り、豊穣関手を通常の関手へ移す。
方針：元の射の一定単体と元の合成の回収を使う。
規約：元の対象と元の射を保持する。
使われ方：非指定自由圏の普遍性を豊穣関手へ移す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

def sourceFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
    C ⥤ ForgetEnrichment SSet.{v} C := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
  exact
    { obj := ForgetEnrichment.of SSet.{v}
      map := fun f => ForgetEnrichment.homOf SSet.{v} (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point f)
      map_id := fun X => ForgetEnrichment.homOf_eId SSet.{v} X
      map_comp := fun {X Y Z} f g => by
        have hc := ForgetEnrichment.homOf_comp SSet.{v}
          (C := C) (X := X) (Y := Y) (Z := Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point g)
        exact (congrArg (ForgetEnrichment.homOf SSet.{v}) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point_comp f g)).symm.trans hc }

variable {D : Type uD} [EnrichedCategory SSet.{v} D]

def ordinaryFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
    EnrichedFunctor SSet.{v} C D → (C ⥤ ForgetEnrichment SSet.{v} D) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory (C := C)
  intro F
  exact sourceFunctor ⋙ F.forget

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
