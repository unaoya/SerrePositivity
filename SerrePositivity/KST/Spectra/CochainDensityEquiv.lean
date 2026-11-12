module

public import SerrePositivity.KST.Spectra.CochainDensityFamilies
public import SerrePositivity.KST.Spectra.CosimplicialTotalization

/-!
概要：通常の Tot への射と完全な重みの end への射の密度による同値。
方針：Tot の普遍性、二添字の族の交換、標準単体の密度、end の普遍性を合成する。
規約：任意のパラメーターについて通常の射の同値を構成する。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。群 cochain と hG の模型比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet


namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {W H : I ⥤ SSet.{u}} {A : SSet.{u}}

lemma fromCochains_toCochains (s : DiagramFamily W H A) :
    fromCochains (toCochains s) = s := by
  apply DiagramFamily.ext
  intro i
  apply Family.ext
  intro n
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (cochainFamily s n))).app i = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
  rfl

lemma toCochains_fromCochains (s : SimplexTensorBoundary.diagram A ⟶
    UnderlyingWeightedCochains.obj (discreteLevels W) H) :
    toCochains (fromCochains s) = s := by
  apply NatTrans.ext
  funext n
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (cochainFamily (fromCochains s) n) = s.app n
  have h : cochainFamily (fromCochains s) n = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (s.app n) := by
    apply NatTrans.ext
    rfl
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_uncurry]

/-- 概要：cochain への標準単体上の射と図式上の密度の族との同値。
方針：各次数の end の両逆と二つの添字の交換を束ねる。
規約：通常の自然変換の同値。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。二重の end の比較。 -/
def cochainFamilyEquiv : (SimplexTensorBoundary.diagram A ⟶
    UnderlyingWeightedCochains.obj (discreteLevels W) H) ≃ DiagramFamily W H A where
  toFun := fromCochains
  invFun := toCochains
  left_inv := toCochains_fromCochains
  right_inv := fromCochains_toCochains

/-- 概要：通常の Tot への射と標準単体上の自然変換との同値。
方針：Tot の end の持ち上げと各成分の uncurry を両逆にする。
規約：余単体図式やパラメーターの Kan 性を要求しない。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Tot の通常の普遍性。 -/
def totalizationHomEquiv (X : CosimplicialObject SSet.{u}) (A : SSet.{u}) :
    (A ⟶ CosimplicialTotalization.obj X) ≃ (SimplexTensorBoundary.diagram A ⟶ X) where
  toFun := CosimplicialTotalization.uncurry
  invFun := CosimplicialTotalization.lift
  left_inv := CosimplicialTotalization.lift_uncurry
  right_inv s := by
    apply NatTrans.ext
    funext n
    change MonoidalClosed.uncurry (CosimplicialTotalization.lift s ≫
      CosimplicialTotalization.π X n) = s.app n
    rw [CosimplicialTotalization.lift_π, uncurry_curry]

/-- 概要：離散的単体の cochain の通常の Tot への射と完全な重みの end への射の同値。
方針：二つの end の普遍性の間に標準単体の密度の同値を挟む。
規約：通常の単体集合の射の同値であり Kan 条件は不要。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。EG の完全な重みとの比較。 -/
def totalizationEndHomEquiv (W H : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (A ⟶ CosimplicialTotalization.obj
      (UnderlyingWeightedCochains.obj (discreteLevels W) H)) ≃
      (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) :=
  (totalizationHomEquiv _ A).trans
    (cochainFamilyEquiv.trans (diagramFamilyEquiv.symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H A).symm))

end

end SerrePositivity.KST.Spectra.SimplexDensity
