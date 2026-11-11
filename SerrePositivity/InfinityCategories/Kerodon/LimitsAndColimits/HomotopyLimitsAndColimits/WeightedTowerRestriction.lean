module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.WeightedTowerKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：成分ごとに anodyne な重みの射が誘導する、塔の end の制限の切断。
方針：全体の切断空間をパラメーターにして普遍的な自然変換を整合的に延長する。
規約：現段階の結論は厳密な右逆の存在であり、両側のホモトピー逆は別の証明対象。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4（Tag 03B5） の重みの比較による標準比較射の検証。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：成分ごとに anodyne な重みの制限は、fibration の塔への end 上で厳密な右逆を持つ。
方針：制限先の end 自体をパラメーターにし、重みの射との直積に沿って普遍切断を延長する。
規約：これだけで制限の同値性やファイバーの可縮性を主張しない。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4.6（Tag 03BB） の重みの比較の実際の逆射の構成。 -/
lemma weightedSectionsPre_tower_exists_section
    {W W' H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W' H,
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) := by
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H
  let j' := j ▷ (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj E
  have hj' (i : AsSmall.{u} ℕᵒᵖ) : anodyneExtensions (j'.app i) :=
    (hj i).whiskerRight E
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_resized_tower_extension_of_anodyne j' hj'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 E))
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b, ?_⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H E).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
  exact hb

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
