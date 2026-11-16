module

public import SerrePositivity.InfinityCategories.Sheaves.TopSieveTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：最大篩の制限形状の恒等射を指定し、その点への制限がleft anodyneであることを示す。
方針：通常の終対象の反対を始対象とし、AsSmallで宇宙を合わせる。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の最大篩の降下。
規約：元の恒等射の点を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 元の恒等射を、大きい宇宙の制限形状の点として指定する。 -/
def topSieveInitialPoint (U : C) : (Δ[0] : SSet.{u+1}) ⟶
    presheafShape (sieveCategory (⊤ : Sieve U)) :=
  nervePoint (AsSmall.up.obj (Opposite.op (topSieveIdentity U)) :
    AsSmall.{u+1} (sieveCategory (⊤ : Sieve U))ᵒᵖ) ≫
      (nerveAsSmallIso (sieveCategory (⊤ : Sieve U))ᵒᵖ).inv

/-- 最大篩の恒等射の点への制限はleft anodyne。 -/
lemma topSieveInitialPoint_leftAnodyne (U : C) :
    leftAnodyneExtensions (topSieveInitialPoint U) := by
  letI : (AsSmall.up : (sieveCategory (⊤ : Sieve U))ᵒᵖ ⥤
      AsSmall.{u+1} (sieveCategory (⊤ : Sieve U))ᵒᵖ).IsEquivalence :=
    (AsSmall.equiv (C := (sieveCategory (⊤ : Sieve U))ᵒᵖ)).isEquivalence_functor
  have hi := (initialOpOfTerminal (topSieveIdentityIsTerminal U)).isInitialObj
    (AsSmall.up : (sieveCategory (⊤ : Sieve U))ᵒᵖ ⥤
      AsSmall.{u+1} (sieveCategory (⊤ : Sieve U))ᵒᵖ)
  exact leftAnodyneExtensions.comp_mem _ _ (nervePoint_leftAnodyne hi)
    (MorphismProperty.of_isIso _ _)

end SerrePositivity.InfinityCategories.Sheaves
