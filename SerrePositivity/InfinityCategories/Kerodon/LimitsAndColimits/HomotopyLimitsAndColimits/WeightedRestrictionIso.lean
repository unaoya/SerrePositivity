module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction
/-!
概要：指定重みの同型を元の重み付き切断の同型へ移す。
方針：同じ前合成射と既存の合成・恒等則を使う。
規約：IS-W2 A12の持ち上げ照合の証明分割。順射の前合成を保持する。
使われ方：HA 1.2.4、Kerodon 7.5.3（Tag 03AP）、AsSmall重みの指定比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {W W' : I ⥤ SSet.{u}}
/-- 指定された重み同型の前合成による、同じ切断空間の同型。 -/
def weightedSectionsWeightIso (e : W ≅ W') (H : I ⥤ SSet.{u}) :
    weightedSections W' H ≅ weightedSections W H where
  hom := weightedSectionsPre e.hom H
  inv := weightedSectionsPre e.inv H
  hom_inv_id := by rw [← weightedSectionsPre_comp, e.inv_hom_id, weightedSectionsPre_id]
  inv_hom_id := by rw [← weightedSectionsPre_comp, e.hom_inv_id, weightedSectionsPre_id]
/-- 同型の順射は指定重み同型の順射による元の前合成。 -/
theorem weightedSectionsWeightIso_hom (e : W ≅ W') (H : I ⥤ SSet.{u}) :
    (weightedSectionsWeightIso e H).hom = weightedSectionsPre e.hom H := rfl
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
