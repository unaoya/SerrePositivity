module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationPrismSimplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationCombinatorics
/-!
概要：実 augmentation の全域切断補正を、単射な添字変更の同じ像へ照合する。
方針：左右の集合・次数を先にそろえ、正しい全域係数の引き戻しを使う。
規約：依存した真の hom の証明引数を書き換えない。使われ方：全実混合係数の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 正しい実内部切断の全域補正は、I 上単射な添字変更の同じ像と一致する。 -/
lemma dgModuleAugmentationHomotopyCut_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1))))
    (j : Fin (m + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F (s.pullback α) I a b k j =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s (I.image α) (α a) (α b) k (α j) := by
  have hamin : IsLeast (I : Set (Fin (m + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (m + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hIL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hIR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  have hiL : Set.InjOn α ((I.filter (· ≤ j)) : Set (Fin (m + 1))) :=
    hi.mono (Finset.filter_subset _ _)
  have hiR : Set.InjOn α ((I.filter (j ≤ ·)) : Set (Fin (m + 1))) :=
    hi.mono (Finset.filter_subset _ _)
  have hLeft := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_left α.monotone hi hj
  have hRight := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_right α.monotone hi hj
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut,
    ← hLeft, ← hRight, Finset.card_image_of_injOn hiL, Finset.card_image_of_injOn hiR]
  simp only [dite_eq_left hsum]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgSimplexHomOrZero_pullback_of_inj s α (I.filter (j ≤ ·)) j b _ hIR
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le _) rfl hiR,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgSimplexHomOrZero_pullback_of_inj s α (I.filter (· ≤ j)) a j _ hIL
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl hiL]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
