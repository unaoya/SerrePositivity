module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeTailMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents

/-!
概要：任意作用素による実 cone の通常成分を、同じ通常末尾面の制限として比較する。
方針：始点を除いた面の全自然性を使い、元の像の集合と端点へ成分を戻す。
規約：潰れた辺の単位分岐も元の通常 nerve の自然性で保持する。
使われ方：全作用素による cone データの pullback の一致。
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
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_pullback_hom_ordinary_map {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((normalizedTensorConeData A X Y c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((normalizedTensorConeData A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
        I a b k hI ha hb hk) := by
  have h0 : (0 : Fin (m + 2)) ∉ I := by
    intro h
    apply ha0
    apply Fin.le_zero_iff.mp
    rw [ha]
    exact I.min'_le 0 h
  let J := withoutFirst I
  have hImage : J.image (Fin.succOrderEmb (m + 1)).toOrderHom = I := by
    change (withoutFirst I).image Fin.succ = I
    rw [image_withoutFirst, Finset.erase_eq_of_notMem h0]
  have hcard : J.card = I.card := by
    have h := congrArg Finset.card hImage
    have hi : Function.Injective (Fin.succOrderEmb (m + 1)).toOrderHom :=
      (Fin.succOrderEmb (m + 1)).injective
    rw [Finset.card_image_of_injective _ hi] at h
    exact h
  have hJ : 2 ≤ J.card := by omega
  have hkJ : k = 2 - (J.card : ℤ) := by rw [hcard]; exact hk
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have hι : ∀ i : Fin (m + 1), (Fin.succOrderEmb (m + 1)).toOrderHom i = i.succ := by
    intro i
    rfl
  have ha' : a'.succ = a := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (Fin.succOrderEmb (m + 1)).toOrderHom.monotone
      (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ).image _)
    have h' : a'.succ = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by simpa only [hImage, hι] using h
    exact h'.trans ha.symm
  have hb' : b'.succ = b := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (Fin.succOrderEmb (m + 1)).toOrderHom.monotone
      (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ).image _)
    have h' : b'.succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by simpa only [hImage, hι] using h
    exact h'.trans hb.symm
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_pullback_eq _ _
    (Fin.succOrderEmb (m + 1)).toOrderHom (Fin.succOrderEmb (m + 1)).toOrderHom
    (normalizedTensorConeData_pullback_tail_map A X Y c θ)
    J a' b' k hJ rfl rfl hkJ (Fin.succ_injective _).injOn (Fin.succ_injective _).injOn
  have hi : Set.InjOn (Fin.succOrderEmb (m + 1)).toOrderHom
      (J : Set (Fin (m + 1))) := (Fin.succ_injective _).injOn
  have ht : ∀ s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) (m + 1),
      HEq (s.hom (J.image (Fin.succOrderEmb (m + 1)).toOrderHom)
        ((Fin.succOrderEmb (m + 1)).toOrderHom a')
        ((Fin.succOrderEmb (m + 1)).toOrderHom b') k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hJ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (Fin.succOrderEmb (m + 1)).toOrderHom.monotone (J.isLeast_min' _) _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (Fin.succOrderEmb (m + 1)).toOrderHom.monotone (J.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hkJ))
        (s.hom I a b k hI ha hb hk) := by
    intro s
    exact s.hom_heq_of_indices_degree hImage ((hι a').trans ha') ((hι b').trans hb') rfl
  exact (ht _).symm.trans (hh.trans (ht _))

end SerrePositivity.EInfinity.ComplexLimits
