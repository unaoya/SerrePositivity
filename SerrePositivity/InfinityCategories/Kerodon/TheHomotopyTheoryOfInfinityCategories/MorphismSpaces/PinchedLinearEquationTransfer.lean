module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearReindex

/-! # 単射による右 pinched 線形方程式の移送

概要：単射な添字変更で線形右辺が像の右辺に一致することを証明する。
方針：削除・右側点数が像と可換であることを有限和の全単射で用いる。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：ホーンの既知面からの方程式の回収。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：集合上単射な引き戻しは線形右辺を保存する。
方針：濃度二以上では所属証明付きの像との全単射で和を移し、削除と符号を比較する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：各面の線形方程式を大域部分集合の方程式に戻す。 -/
lemma pullback_rhs_of_inj {m n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f).rhs J k hk =
      f.rhs (J.image α) k (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  have hc : (J.image α).card = J.card := Finset.card_image_of_injOn hi
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
  by_cases hJ : 2 ≤ J.card
  · have hI : 2 ≤ (J.image α).card := by rw [hc]; exact hJ
    rw [dite_eq_left hJ, dite_eq_left hI]
    let e : J → J.image α := fun j => ⟨α j.val, Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩⟩
    have he : Function.Bijective e := by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact hi a.property b.property (congrArg Subtype.val hab)
      · intro b
        obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp b.property
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
    refine Fintype.sum_bijective e he _ _ ?_
    intro j
    have hiE : Set.InjOn α ((J.erase j.val) : Set (Fin (m + 1))) :=
      hi.mono (by intro a ha; exact (Finset.mem_erase.mp ha).2)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ hiE]
    dsimp only [e]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_sign_card α.monotone hi j.property]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_erase hi j.property]
  · have hI : ¬ 2 ≤ (J.image α).card := by rwa [hc]
    rw [dite_eq_right hJ, dite_eq_right hI]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pullback_rhs_of_inj)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
