module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationResolution

/-!
概要：実際に構成した任意辺集合の局所化を、元の quasicategory と射として公開する。
方針：証明済みの同宇宙の存在定理から選び、全関手 ∞ 圏の普遍性を保持する。
規約：安定圏の商の安定性・完全性は仮定も結論もしていない。
使われ方：一般の Verdier 商の候補への後続の幾何的な証明。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (X : SSet.{u}) (W : Set (X _⦋1⦌))

def edgeLocalization : SSet.{u} := Classical.choose (exists_quasicategory_localization X W)

def edgeLocalizationMap : X ⟶ edgeLocalization X W :=
  Classical.choose (Classical.choose_spec (exists_quasicategory_localization X W))

instance edgeLocalization_quasicategory : Quasicategory (edgeLocalization X W) :=
  (Classical.choose_spec (Classical.choose_spec (exists_quasicategory_localization X W))).1

lemma edgeLocalization_isLocalization : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (edgeLocalizationMap X W) W :=
  (Classical.choose_spec (Classical.choose_spec (exists_quasicategory_localization X W))).2

lemma edgeLocalization_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (edgeLocalizationMap X W) W :=
  (edgeLocalization_isLocalization X W).choose

lemma edgeLocalization_universal (Y : SSet.{u}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (edgeLocalizationMap X W) W
      (edgeLocalization_inverts X W) Y) :=
  (edgeLocalization_isLocalization X W).choose_spec Y

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
