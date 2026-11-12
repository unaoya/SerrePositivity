module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedTowerRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCorner
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：fibration の塔の end の重みの anodyne な制限は trivial Kan fibration。
方針：全境界の持ち上げ問題を重みと境界の pushout-product に移し、塔の整合的延長を使う。
規約：重みの制限そのものについて全境界を充填し、切断の存在だけで同値性を代用しない。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4.6（Tag 03BB） の homotopy 極限の重みの比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：成分ごとに anodyne な重みの射による塔の end の制限は trivial Kan fibration。
方針：境界と重みの制限で整合する二つの自然変換を pushout 上で貼り、成分ごとの anodyne 性で延長。
規約：零段の Kan 性と全ての隣接遷移の Fibration 性を前提とする。
使われ方：Kerodon 7.5.3（Tag 03AP）、γ3 の重みの比較の全境界の持ち上げ。 -/
lemma weightedSectionsPre_tower_trivialKanFibration
    {W W' H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro t s sq
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner j (boundary n).ι
  have hw : (j ▷ (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (boundary n : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t =
      (W ◁ (Functor.const (AsSmall.{u} ℕᵒᵖ)).map (boundary n).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry s := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry sq.w
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp] at h
    exact h
  let a := P.isPushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry s) hw
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_resized_tower_extension_of_anodyne P.ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner_obj_anodyne j hj (boundary n).ι) a
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b, fac_left := ?_, fac_right := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W' H (boundary n : SSet.{u})).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry ((boundary n).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    calc
      _ = (P.inl ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inl_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inl_desc _ _ _
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H (Δ[n] : SSet.{u})).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    calc
      _ = (P.inr ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inr_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inr_desc _ _ _

/-- 概要：成分ごとに anodyne な重みの制限は塔の end の実際のホモトピー同値。
方針：構成した全境界の持ち上げ性を既存の trivial Kan fibration の同値判定へ渡す。
規約：両側の end の Kan 性も証明済みの塔の充填から得る。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4.6（Tag 03BB） の重みの比較。 -/
lemma weightedSectionsPre_tower_homotopyEquivalence
    {W W' H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex W H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex W' H
  have := weightedSectionsPre_tower_trivialKanFibration (H := H) j hj
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
