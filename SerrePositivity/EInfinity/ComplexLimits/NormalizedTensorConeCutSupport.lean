module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeNonedgeCut
public import SerrePositivity.EInfinity.ComplexLimits.ConePenultimate
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryDecomposition

/-!
概要：実 cone の HA 切断合成は、元の有限集合の最後から二番目以外で零である。
方針：元の項の二つの分解を相殺し、二点右切断の一意性を使う。
規約：全ての次数と元の内部点を保持する。
使われ方：混合右辺の全非線形部分を一つの切断へ還元する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_cutCompose_of_nonedge {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hc : (I.filter (j ≤ ·)).card ≠ 2) :
    (normalizedTensorConeData A X Y c).cutCompose I a b k j = 0 := by
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.term_eq_linear_sub_cut
    (normalizedTensorConeData A X Y c) I a b k hI ha hb hk j hj haj hjb
  have h₂ := normalizedTensorConeData_term_of_nonedge_cut A X Y c I a b k hI ha hb hk
    j hj haj hjb hc
  have h := congrArg (fun v => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j)⁻¹ • v) (h₁.symm.trans h₂)
  simp only [smul_smul, inv_mul_cancel, one_smul] at h
  exact sub_eq_self.mp h

lemma normalizedTensorConeData_cutCompose_of_ne_penultimate {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hne : j ≠ penultimate I hI) :
    (normalizedTensorConeData A X Y c).cutCompose I a b k j = 0 := by
  apply normalizedTensorConeData_cutCompose_of_nonedge A X Y c I a b k hI ha hb hk j hj haj hjb
  intro hc
  exact hne ((right_card_two_iff_penultimate I hI j hj (by rw [← hb]; exact hjb)).mp hc)

end SerrePositivity.EInfinity.ComplexLimits
