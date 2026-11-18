module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：部分集合上で等しい作用素の引き戻し成分、および定値作用素の全データを比較する。
方針：全成分・全切断・微分の比較を端点の等式輸送と両立させる。
規約：元の実単体と同じ対象・次数を保持する。使われ方：大域評価三角形の全 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

lemma simplexData_pullback_hom_eqOn {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (α β : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (he : ∀ i ∈ I, α i = β i) :
    HEq ((s.pullback α).hom I a b k hI ha hb hk)
      ((s.pullback β).hom I a b k hI ha hb hk) := by
  have hi : Set.InjOn α (I : Set (Fin (m + 1))) ↔ Set.InjOn β (I : Set (Fin (m + 1))) := by
    constructor
    · intro h i hii j hjj hij
      exact h hii hjj ((he i hii).trans (hij.trans (he j hjj).symm))
    · intro h i hii j hjj hij
      exact h hii hjj ((he i hii).symm.trans (hij.trans (he j hjj)))
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  by_cases hα : Set.InjOn α (I : Set (Fin (m + 1)))
  · have hβ := hi.mp hα
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hβ]
    apply s.hom_heq_of_indices_degree
    · exact Finset.image_congr he
    · exact he a haI
    · exact he b hbI
    · rfl
  · have hβ : ¬ Set.InjOn β (I : Set (Fin (m + 1))) := fun h => hα (hi.mpr h)
    by_cases hc : I.card = 2
    · have hu : ∀ {x y : D} (h : x = y),
          HEq (unitElement A x).val (unitElement A y).val := by
        intro x y h
        cases h
        rfl
      exact (s.pullback_hom_of_collapsed_pair α I a b k hI ha hb hk hα hc).trans
        ((hu (congrArg s.obj (he b hbI))).trans
          (s.pullback_hom_of_collapsed_pair β I a b k hI ha hb hk hβ hc).symm)
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hα hc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hβ hc]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (congrArg s.obj (he a haI)) (congrArg s.obj (he b hbI)) rfl

lemma simplexData_pullback_const {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (i : Fin (n + 1)) :
    s.pullback (OrderHom.const (Fin (m + 1)) i) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) (s.obj i)).toSimplexData.pullback
        (OrderHom.const (Fin (m + 1)) (0 : Fin 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    apply eq_of_heq
    have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
    have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
    have hab : a ≠ b := by rw [ha, hb]; exact (I.min'_lt_max'_of_card (by omega)).ne
    have hni : ∀ {l : ℕ} (j : Fin (l + 1)),
        ¬ Set.InjOn (OrderHom.const (Fin (m + 1)) j) (I : Set (Fin (m + 1))) := by
      intro l j hi
      exact hab (hi haI hbI rfl)
    by_cases hc : I.card = 2
    · exact (s.pullback_hom_of_collapsed_pair _ I a b k hI ha hb hk (hni i) hc).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) (s.obj i)).toSimplexData.pullback_hom_of_collapsed_pair
          _ I a b k hI ha hb hk (hni (0 : Fin 1)) hc).symm
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ (hni i) hc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ (hni (0 : Fin 1)) hc]
end SerrePositivity.ComplexLimits
