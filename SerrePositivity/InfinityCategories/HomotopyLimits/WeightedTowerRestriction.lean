module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedTowerKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedRestriction

/-!
概要：成分ごとに anodyne な重みの射が誘導する、塔の end の制限の切断。
方針：全体の切断空間をパラメーターにして普遍的な自然変換を整合的に延長する。
規約：現段階の結論は厳密な右逆の存在であり、両側のホモトピー逆は別の証明対象。
使われ方：Kerodon 7.5.3、7.5.4 の重みの比較による標準比較射の検証。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：成分ごとに anodyne な重みの制限は、fibration の塔への end 上で厳密な右逆を持つ。
方針：制限先の end 自体をパラメーターにし、重みの射との直積に沿って普遍切断を延長する。
規約：これだけで制限の同値性やファイバーの可縮性を主張しない。
使われ方：Kerodon 7.5.3、7.5.4.6 の重みの比較の実際の逆射の構成。 -/
lemma weightedSectionsPre_tower_exists_section
    {W W' H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    ∃ s : weightedSections W H ⟶ weightedSections W' H,
      s ≫ weightedSectionsPre j H = 𝟙 (weightedSections W H) := by
  let E := weightedSections W H
  let j' := j ▷ (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj E
  have hj' (i : AsSmall.{u} ℕᵒᵖ) : anodyneExtensions (j'.app i) :=
    (hj i).whiskerRight E
  obtain ⟨b, hb⟩ := exists_resized_tower_extension_of_anodyne j' hj'
    (weightedSectionsUncurry (𝟙 E))
  refine ⟨weightedSectionsLift b, ?_⟩
  apply (weightedSectionsHomEquiv W H E).injective
  change weightedSectionsUncurry (weightedSectionsLift b ≫ weightedSectionsPre j H) = _
  rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_lift]
  exact hb

end SerrePositivity.InfinityCategories.HomotopyLimits
