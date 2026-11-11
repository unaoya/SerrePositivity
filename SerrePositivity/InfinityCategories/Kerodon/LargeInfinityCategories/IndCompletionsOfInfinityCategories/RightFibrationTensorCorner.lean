module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightFibrationPrismCorner

/-!
概要：right fibration で、一般の形状包含と right anodyne な側面を同時に保って持ち上げる。
方針：元の二境界を pushout-product で貼り、right anodyne 性で延長する。
規約：元の全底図式と両全境界を保持し、モデル圏を仮定しない。
使われ方：有限半順序形状の点追加における全 slice 円柱。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の全積図式を、指定された二境界を保って持ち上げる。
方針：right anodyne な pushout-product。規約：元の全射。使われ方：点追加の補間。 -/
lemma exists_rightFibration_tensor_corner_lift {A D K K₀ E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (j : D ⟶ A) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j)
    (k : K₀ ⟶ K) [Mono k] (b : A ⊗ K ⟶ B)
    (a : A ⊗ K₀ ⟶ E) (d : D ⊗ K ⟶ E)
    (h : (j ▷ K₀) ≫ a = (D ◁ k) ≫ d)
    (ha : a ≫ p = (A ◁ k) ≫ b) (hd : d ≫ p = (j ▷ K) ≫ b) :
    ∃ W : A ⊗ K ⟶ E,
      W ≫ p = b ∧ (A ◁ k) ≫ W = a ∧ (j ▷ K) ≫ W = d := by
  let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) j k
  have hl : sq.inl ≫ sq.ι = A ◁ k := sq.inl_ι
  have hr : sq.inr ≫ sq.ι = j ▷ K := sq.inr_ι
  let t := sq.isPushout.desc a d h
  have ht : t ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.isPushout.inl_desc, ha, ← hl, Category.assoc]
    · rw [← Category.assoc, sq.isPushout.inr_desc, hd, ← hr, Category.assoc]
  have : HasLiftingProperty sq.ι p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightAnodyne_pushoutObjObj_left j hj k sq p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p))
  let L : CommSq t sq.ι p b := ⟨ht⟩
  refine ⟨L.lift, L.fac_right, ?_, ?_⟩
  · rw [← hl, Category.assoc, L.fac_left, sq.isPushout.inl_desc]
  · rw [← hr, Category.assoc, L.fac_left, sq.isPushout.inr_desc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
