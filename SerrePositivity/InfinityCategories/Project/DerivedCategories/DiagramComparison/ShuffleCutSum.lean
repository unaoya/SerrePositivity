module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutValues

/-!
概要：対角切断での符号付き shuffle の和を、二因子の元の Moore 射影へ簡約する。
方針：前半が非単射の項を消し、唯一残る初期水平格子路の値と符号を使う。
規約：元の整数テンソルと指定射影を保持する。
使われ方：HA 1.2.4、G10 の正規化 shuffle→AW の成分の合成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 対角切断の符号付き和は元の二因子の射影である。 -/
theorem shuffleCut_diagonal_sum (C D : SimplicialObject (ModuleCat.{u} ℤ))
    (p n : ℕ) (hp : p ≤ n) :
    (∑ s : ShuffleIndex p n, (-1 : ℤ) ^ s.inversions •
      integerTensorMap
        (C.map (awFront n ⟨p, Nat.lt_succ_of_le hp⟩ ≫ s.left).op ≫
          (PInftyToNormalizedMooreComplex C).f p)
        (D.map (awBack n ⟨p, Nat.lt_succ_of_le hp⟩ ≫
          s.right (Nat.add_sub_of_le hp)).op ≫
          (PInftyToNormalizedMooreComplex D).f (n - p))) =
    integerTensorMap ((PInftyToNormalizedMooreComplex C).f p)
      ((PInftyToNormalizedMooreComplex D).f (n - p)) := by
  rw [Finset.sum_eq_single (initialShuffle p n hp)]
  · rw [initialShuffle_sign, one_smul, initialShuffle_front, initialShuffle_back]
    simp only [op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · intro s hs hne
    have hn : ¬ Mono (awFront n ⟨p, Nat.lt_succ_of_le hp⟩ ≫ s.left) := by
      intro hm
      exact hne (shuffle_eq_initial_of_front_mono hp s)
    rw [degeneracy_comp_mooreProjection C p _ hn, integerTensorMap_zero_left, smul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- 元の shuffle 成分と正規化した対角切断の合成。 -/
theorem shuffleBidegree_diagonal_projection
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) (p n : ℕ) (hp : p ≤ n) :
    shuffleBidegree C D p (n - p) n (Nat.add_sub_of_le hp) ≫
      integerTensorMap
        (C.map (awFront n ⟨p, Nat.lt_succ_of_le hp⟩).op ≫
          (PInftyToNormalizedMooreComplex C).f p)
        (D.map (awBack n ⟨p, Nat.lt_succ_of_le hp⟩).op ≫
          (PInftyToNormalizedMooreComplex D).f (n - p)) =
      integerTensorMap ((PInftyToNormalizedMooreComplex C).f p)
        ((PInftyToNormalizedMooreComplex D).f (n - p)) := by
  rw [shuffleBidegree, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ← integerTensorMap_comp, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← op_comp]
  exact shuffleCut_diagonal_sum C D p n hp

/-- 元の shuffle 成分と異なる次数の正規化切断の合成は零。 -/
theorem shuffleBidegree_offDiagonal_projection
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) {p q n : ℕ} (h : p + q = n)
    (i : Fin (n + 1)) (hi : (i : ℕ) ≠ p) :
    shuffleBidegree C D p q n h ≫
      integerTensorMap
        (C.map (awFront n i).op ≫ (PInftyToNormalizedMooreComplex C).f i)
        (D.map (awBack n i).op ≫ (PInftyToNormalizedMooreComplex D).f (n - i)) = 0 := by
  rw [shuffleBidegree, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Preadditive.zsmul_comp, ← integerTensorMap_comp]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp]
  rw [shuffleCut_tensor_zero C D h s i hi, smul_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
