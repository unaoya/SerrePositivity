module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-!
概要：小さい site の前層形状と、同じ AsSmall 表示の反対 nerve を厳密に比較する。
方針：全合成可能射列へ AsSmall.up.op と AsSmall.down.op を後合成する。
  文献対応：HTT 1.2.7.3、Kerodon §4.5.1（Tag 01DQ）の形状の宇宙表示の変更。
規約：係数は SSet(u+1) のまま、反対圏と持ち上げの順序を明示する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves

/-- AsSmall と反対圏の順序を変える、既存の通常圏の同値の合成。 -/
def asSmallOppositeEquivalence (C : Type u) [SmallCategory C] :
    AsSmall.{u + 1} Cᵒᵖ ≌ (AsSmall.{u + 1} C)ᵒᵖ :=
  (AsSmall.equiv (C := Cᵒᵖ)).symm.trans (AsSmall.equiv (C := C)).op

/-- 同じ全単体の AsSmall 表示による、小さい site の形状の厳密な同型。 -/
def asSmallSiteShapeIso (C : Type u) [SmallCategory C] :
    presheafShape C ≅ nerve (AsSmall.{u + 1} C)ᵒᵖ where
  hom :=
    { app := fun _ ↦ ↾fun σ ↦ σ.down ⋙ AsSmall.up.op
      naturality := fun _ _ _ ↦ rfl }
  inv :=
    { app := fun _ ↦ ↾fun σ ↦ ULift.up (σ ⋙ AsSmall.down.op)
      naturality := fun _ _ _ ↦ rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- nerve と opposite の順序を変えても、元の同じ全単体の比較射となる。 -/
lemma asSmallSiteShapeIso_hom (C : Type u) [SmallCategory C] :
    (nerveAsSmallIso.{u, u + 1} Cᵒᵖ).hom ≫
      nerveMap (asSmallOppositeEquivalence C).functor = (asSmallSiteShapeIso C).hom := rfl

end SerrePositivity.InfinityCategories.Sheaves
