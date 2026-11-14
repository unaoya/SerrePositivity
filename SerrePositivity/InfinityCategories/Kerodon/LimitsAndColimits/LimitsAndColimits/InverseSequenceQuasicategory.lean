module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InverseSequenceRelativeLifting
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.FibrationTowerLimitCone

/-!
概要：inner fibration の可算の塔の極限は quasicategory。
方針：既存の具体的な整合族の塔の右持ち上げを、任意の極限錐へ同型で移す。
規約：モデル構造を仮定せず、任意の左射に対する持ち上げ補題だけを使う。
使われ方：可算骨格の反転関手と同時解像の極限の同値判定。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet Opposite
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- inner fibration の可算の塔の初段への射影も inner fibration。 -/
lemma innerFibration_inverseSequence_projection_zero (F : ℕᵒᵖ ⥤ SSet.{u})
    (c : Cone F) (hc : IsLimit c)
    [∀ n, InnerFibration (F.map (homOfLE (Nat.le_succ n)).op)] :
    InnerFibration (c.π.app (op 0)) := by
  let X := fun n ↦ F.obj (op n)
  let d := fun n ↦ F.map (homOfLE (Nat.le_succ n)).op
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0
  have : InnerFibration p := by
    constructor
    intro U V i hi
    have : ∀ n, HasLiftingProperty i (d n) := fun n ↦
      InnerFibration.mem (q := d n) i hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_zero_hasLiftingProperty X d i
  let e := hc.conePointUniqueUpToIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit F)
  have he : e.hom ≫ p = c.π.app (op 0) :=
    hc.conePointUniqueUpToIso_hom_comp
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit F) (op 0)
  rw [← he]
  exact ⟨innerFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ e.hom)
    (mem_innerFibrations p)⟩

/-- 初段が quasicategory で全遷移が inner fibration なら、任意の極限錐の頂点もそうなる。 -/
lemma quasicategory_of_inverseSequence_limit (F : ℕᵒᵖ ⥤ SSet.{u})
    (c : Cone F) (hc : IsLimit c) [Quasicategory (F.obj (op 0))]
    [∀ n, InnerFibration (F.map (homOfLE (Nat.le_succ n)).op)] : Quasicategory c.pt := by
  have := innerFibration_inverseSequence_projection_zero F c hc
  exact quasicategory_of_innerFibration (c.π.app (op 0))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
