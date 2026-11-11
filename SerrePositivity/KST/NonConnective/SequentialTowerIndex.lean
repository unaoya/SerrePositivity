module

public import SerrePositivity.KST.NonConnective.SequentialIndexFunctors
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex

/-!
概要：元の逐次添字の反対と、既存の可算塔の添字の厳密な比較。
方針：自然数の上下の関手を反対と AsSmall に合わせる。
規約：nerve の実同型と圏同値の双方を保持する。
使われ方：元の反変 Hom 錐を既存の塔の極限定理へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective

/-- 標準の可算塔の添字から元の逐次添字の反対への実関手。 -/
def sequentialTowerIndex : AsSmall.{u} ℕᵒᵖ ⥤ SequentialIndex.{u}ᵒᵖ :=
  AsSmall.down ⋙ sequentialIndexUp.op

/-- 元の逐次添字の反対と標準可算塔の添字の圏同値。 -/
def sequentialTowerIndexEquivalence : AsSmall.{u} ℕᵒᵖ ≌ SequentialIndex.{u}ᵒᵖ where
  functor := sequentialTowerIndex
  inverse := sequentialIndexDown.op ⋙ AsSmall.up
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro _ _ _
    rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro _ _ _
    rfl)

/-- 元の添字への再添字の nerve は、全単体での実際の同型。 -/
instance sequentialTowerIndex_nerveMap_isIso : IsIso (nerveMap sequentialTowerIndex.{u}) := by
  let H := sequentialIndexDown.op ⋙ AsSmall.up
  refine ⟨nerveMap H, ?_, ?_⟩
  all_goals
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end SerrePositivity.KST.NonConnective
