module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeSimplexData
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageCycles

/-! # 元の native HA 成分データの全二点方程式
概要：実 dg 関手から取り出した元の全二点成分は閉じ、同じ HA 方程式を満たす。
方針：元の零次元 Serre 生成元の閉性と、二点集合に内部頂点が無いことを使う。
規約：全次数・端点の元の証明引数を保持。使われ方：native 単体比較の基底方程式。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実 dg 関手の native HA 成分データの全二点成分は閉じている。 -/
lemma cubicalLambdaNativeSimplexData_two_closed {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (hcard : I.card = 2) :
    differential A ((cubicalLambdaNativeSimplexData A F).hom I
      (I.min' (Finset.card_pos.mp (by omega))) (I.max' (Finset.card_pos.mp (by omega)))
      (2 - (I.card : ℤ)) hI rfl rfl rfl) = 0 := by
  have hgen := serreCubeTopCellImage_cast_zero_d A _ (I.card - 2) (by omega)
    (simplexSubsetLambdaCell A I hI) (2 - (I.card : ℤ)) (by omega)
  change differential A (simplexSubsetLambdaGenerator A I hI) = 0 at hgen
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential F (simplexSubsetLambdaGenerator A I hI)).symm.trans
    ((congrArg (fun x => (F.map _ _).f (2 - (I.card : ℤ) + 1) x) hgen).trans (map_zero _))

/-- 元の実 dg 関手の native HA 成分データは、元の全二点集合で同じ HA 方程式を満たす。 -/
lemma cubicalLambdaNativeSimplexData_equation_two {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hcard : I.card = 2) :
    differential A ((cubicalLambdaNativeSimplexData A F).hom I a b k hI ha hb hk) =
      (cubicalLambdaNativeSimplexData A F).rhs I a b k hI ha hb hk := by
  subst a
  subst b
  subst k
  have hz : (cubicalLambdaNativeSimplexData A F).rhs I
      (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
      (2 - (I.card : ℤ)) hI rfl rfl rfl = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · exfalso
      let a := I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
      let b := I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
      change a < j.val ∧ j.val < b at h
      have hsub : ({a, j.val, b} : Finset (Fin (n + 1))) ⊆ I := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact I.min'_mem _
        · exact j.property
        · exact I.max'_mem _
      have h3 : ({a, j.val, b} : Finset (Fin (n + 1))).card = 3 := by
        simp [ne_of_lt h.1, ne_of_lt h.2, ne_of_lt (h.1.trans h.2)]
      have hle := Finset.card_le_card hsub
      omega
    · rfl
  exact (cubicalLambdaNativeSimplexData_two_closed A F I hI hcard).trans hz.symm

end SerrePositivity.KST.SConstruction
