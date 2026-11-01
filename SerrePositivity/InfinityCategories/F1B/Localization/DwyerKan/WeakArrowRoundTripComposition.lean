module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WeakArrowCancellationHomotopy
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitRowComposition

/-!
# 指定射の往復行と元の豊穣合成の一致

概要：往復行の一定写像を forward・backward の元の合成へ照合する。
方針：一般の行の連結と合成の回収式を適用する。
規約：既存の arrowMap・colimitComposition をそのまま使う。
使われ方：指定射による前後合成のホモトピー逆。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WeakArrow
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} (g : X ⟶ Y) (hg : W g)

lemma sourceRoundTrip_composition : colimitRowMap (sourceRoundTrip g hg) =
    (λ_ (𝟙_ SSet.{max u v})).inv ≫ (arrowMap W g ⊗ₘ backwardMap g hg) ≫
      colimitComposition W X Y X :=
  colimitRowMap_append (ForwardZigzag.obj g) (BackwardZigzag.obj g hg)

lemma targetRoundTrip_composition : colimitRowMap (targetRoundTrip g hg) =
    (λ_ (𝟙_ SSet.{max u v})).inv ≫ (backwardMap g hg ⊗ₘ arrowMap W g) ≫
      colimitComposition W Y X Y :=
  colimitRowMap_append (BackwardZigzag.obj g hg) (ForwardZigzag.obj g)

def sourceCompositeHomotopy : SSet.Homotopy (colimitUnit W X)
    ((λ_ (𝟙_ SSet.{max u v})).inv ≫ (arrowMap W g ⊗ₘ backwardMap g hg) ≫
      colimitComposition W X Y X) := by
  rw [← sourceRoundTrip_composition]
  exact sourceCancellationHomotopy g hg

def targetCompositeHomotopy : SSet.Homotopy
    ((λ_ (𝟙_ SSet.{max u v})).inv ≫ (backwardMap g hg ⊗ₘ arrowMap W g) ≫
      colimitComposition W Y X Y) (colimitUnit W Y) := by
  rw [← targetRoundTrip_composition]
  exact targetCancellationHomotopy g hg

end SerrePositivity.EInfinity.Hammock.WeakArrow
