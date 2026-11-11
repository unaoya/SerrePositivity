module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex

/-!
概要：両端の像が異なる非単射引き戻しの全 cochain は零になる。
方針：元の非単射添字・同相の二点・切断の一意性を使う。
規約：主場合の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

lemma simplexData_pullback_hom_zero_of_not_inj_of_ne {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) (hne : α a ≠ α b) :
    (s.pullback α).hom I a b k hI ha hb hk = 0 := by
  apply s.pullback_hom_of_not_inj α I a b k hI ha hb hk hi
  intro hc
  exact hne (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc (by rw [ha]; exact I.isLeast_min' _)
    (by rw [hb]; exact I.isGreatest_max' _))
end SerrePositivity.EInfinity.ComplexLimits
