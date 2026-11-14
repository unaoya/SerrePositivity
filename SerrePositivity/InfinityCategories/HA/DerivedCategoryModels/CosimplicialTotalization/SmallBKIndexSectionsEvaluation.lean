module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SmallBKIndexSections

/-!
概要：同じsmall BK添字移送は元のuncurryの各点評価を保つ。
方針：既存のend射影の添字制限則をuncurryする。
規約：IS-W2 B02の既存構成の自然性。重みと全パラメータを変更しない。
使われ方：HA 1.2.4、元の指定反転BK比較への添字輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 添字を制限してからのuncurryは、同じ元の対象でのuncurryと一致。 -/
theorem smallBKIndexSectionsMap_uncurry {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections W H) (j : J) :
    (weightedSectionsUncurry (f ≫ smallBKIndexSectionsMap F W H)).app j =
      (weightedSectionsUncurry f).app (F.obj j) := by
  change uncurry ((f ≫ smallBKIndexSectionsMap F W H) ≫
    weightedSectionsπ (F ⋙ W) (F ⋙ H) j) = _
  rw [Category.assoc, smallBKIndexSectionsMap_π]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
