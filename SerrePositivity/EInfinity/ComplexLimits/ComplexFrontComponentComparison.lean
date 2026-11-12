module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeFront
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRecoverIndex

/-!
概要：二つの実複体単体データの前面が一致すれば、終端を避ける全成分は一致する。
方針：同じ前面へ集合を戻し、単射制限の成分比較を元の集合へ移送する。
規約：方程式を仮定しない。使われ方：二重 cone の通常成分の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexSimplexData_hom_heq_of_front_eq {m : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) (m + 1))
    (hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b ≠ Fin.last (m + 1)) :
    HEq (s.hom I a b k hI ha hb hk) (t.hom I a b k hI ha hb hk) := by
  have hn : Fin.last (m + 1) ∉ I := by
    intro hl
    apply hbl
    apply le_antisymm (Fin.le_last _)
    rw [hb]
    exact I.le_max' _ hl
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I
  have hImage : J.image Fin.castSuccOrderEmb.toOrderHom = I := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I).image Fin.castSucc = I
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withoutLast, Finset.erase_eq_of_notMem hn]
  have hcard : J.card = I.card := by
    have h := congrArg Finset.card hImage
    have hi : Function.Injective
        (Fin.castSuccOrderEmb.toOrderHom : Fin (m + 1) →o Fin (m + 2)) :=
      (Fin.castSucc_injective _)
    rw [Finset.card_image_of_injective _ hi] at h
    exact h
  have hJ : 2 ≤ J.card := by omega
  have hkJ : k = 2 - (J.card : ℤ) := by rw [hcard]; exact hk
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have hι : ∀ i : Fin (m + 1), Fin.castSuccOrderEmb.toOrderHom i = i.castSucc := by
    intro i
    rfl
  have ha' : a'.castSucc = a := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min Fin.castSuccOrderEmb.toOrderHom.monotone
      (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ).image _)
    have h' : a'.castSucc = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by simpa only [hImage, hι] using h
    exact h'.trans ha.symm
  have hb' : b'.castSucc = b := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max Fin.castSuccOrderEmb.toOrderHom.monotone
      (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ).image _)
    have h' : b'.castSucc = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by simpa only [hImage, hι] using h
    exact h'.trans hb.symm
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_pullback_eq s t
    Fin.castSuccOrderEmb.toOrderHom Fin.castSuccOrderEmb.toOrderHom hfront
    J a' b' k hJ rfl rfl hkJ (Fin.castSucc_injective _).injOn (Fin.castSucc_injective _).injOn
  have hi : Set.InjOn Fin.castSuccOrderEmb.toOrderHom (J : Set (Fin (m + 1))) :=
    (Fin.castSucc_injective _).injOn
  have ht : ∀ r : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) (m + 1),
      HEq (r.hom (J.image Fin.castSuccOrderEmb.toOrderHom)
        (Fin.castSuccOrderEmb.toOrderHom a') (Fin.castSuccOrderEmb.toOrderHom b') k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hJ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min Fin.castSuccOrderEmb.toOrderHom.monotone (J.isLeast_min' _) _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max Fin.castSuccOrderEmb.toOrderHom.monotone (J.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hkJ))
        (r.hom I a b k hI ha hb hk) := by
    intro r
    exact r.hom_heq_of_indices_degree hImage ((hι a').trans ha') ((hι b').trans hb') rfl
  exact (ht s).symm.trans (hh.trans (ht t))

end SerrePositivity.EInfinity.ComplexLimits
