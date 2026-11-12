module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakArrowCancellationHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition

/-!
# 指定射の往復行と元の豊穣合成の一致

概要：往復行の一定写像を forward・backward の元の合成へ照合する。
方針：一般の行の連結と合成の回収式を適用する。
規約：既存の arrowMap・colimitComposition をそのまま使う。
使われ方：指定射による前後合成のホモトピー逆。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} (g : X ⟶ Y) (hg : W g)

lemma sourceRoundTrip_composition : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceRoundTrip g hg) =
    (λ_ (𝟙_ SSet.{max u v})).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.colimitRowMap_append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj g hg)

lemma targetRoundTrip_composition : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetRoundTrip g hg) =
    (λ_ (𝟙_ SSet.{max u v})).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W Y X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.colimitRowMap_append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj g hg) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g)

def sourceCompositeHomotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X)
    ((λ_ (𝟙_ SSet.{max u v})).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y X) := by
  rw [← sourceRoundTrip_composition]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceCancellationHomotopy g hg

def targetCompositeHomotopy : SSet.Homotopy
    ((λ_ (𝟙_ SSet.{max u v})).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W Y X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W Y) := by
  rw [← targetRoundTrip_composition]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetCancellationHomotopy g hg

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
