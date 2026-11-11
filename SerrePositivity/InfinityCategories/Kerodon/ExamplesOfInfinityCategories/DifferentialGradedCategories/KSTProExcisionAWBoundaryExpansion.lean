module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWTensorDifferential
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.KSTProExcisionAWBoundaryIndex

/-!
# AW の全切断点の境界和

概要：各切断点の水平・垂直微分の公式を AW の有限和へ適用する。
方針：水平側は最初の切断点、垂直側は最後の切断点を除いて面の和に展開する。
規約：KST Construction A.5 の標準 AW、非被約な零次の因子を含む。
使われ方：非対角項の添字変換と対角項の相殺による鎖写像性の証明。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：零以外の切断点での AW の水平境界の展開。
方針：第一因子の次数を i+1 として斉次制限項の水平微分を適用する。
規約：KST A.5、第一因子の全ての面を含む。
使われ方：水平境界の非対角と対角への分解。 -/
lemma alexanderWhitneySummand_succ_D₁ (n : ℕ) (i : Fin (n + 1)) :
    alexanderWhitneySummand C D (n + 1) i.succ ≫
      mapBifunctor.D₁ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n =
    ∑ k : Fin ((i : ℕ) + 2), (-1 : ℤ) ^ (k : ℕ) •
      awTensorTerm C D (SimplexCategory.δ k ≫ awFront (n + 1) i.succ)
        (awBack (n + 1) i.succ) (by have := i.isLt; simp only [Fin.val_succ]; omega) := by
  exact awTensorTerm_D₁ C D (awFront (n + 1) i.succ) (awBack (n + 1) i.succ)
    (by have := i.isLt; simp only [Fin.val_succ]; omega)

/-- 概要：AW の水平微分全体を零でない切断点の面の二重和へ展開する。
方針：最初の切断点の水平微分は零で、残りに斉次成分の公式を適用する。
規約：KST Construction A.5、零次の第一因子を正しく含める。
使われ方：水平境界の非対角項の添字変換。 -/
lemma alexanderWhitney_horizontal_boundary (n : ℕ) :
    alexanderWhitneyApp C D (n + 1) ≫
      mapBifunctor.D₁ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n =
    ∑ i : Fin (n + 1), ∑ k : Fin ((i : ℕ) + 2), (-1 : ℤ) ^ (k : ℕ) •
      awTensorTerm C D (SimplexCategory.δ k ≫ awFront (n + 1) i.succ)
        (awBack (n + 1) i.succ) (by have := i.isLt; simp only [Fin.val_succ]; omega) := by
  rw [alexanderWhitneyApp, Preadditive.sum_comp, Fin.sum_univ_succ]
  have hz : alexanderWhitneySummand C D (n + 1) 0 ≫
      mapBifunctor.D₁ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n = 0 :=
    awTensorTerm_zero_D₁ C D (awFront (n + 1) 0) (awBack (n + 1) 0) (awDegrees (n + 1) 0)
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  exact alexanderWhitneySummand_succ_D₁ C D n i

/-- 概要：最後以外の切断点での AW の垂直境界の展開。
方針：後半の長さを q+1 に書き、斉次制限項の垂直微分を適用する。
規約：KST A.5、垂直符号は切断点 i の番号。
使われ方：垂直境界の非対角項と対角項への分解。 -/
lemma alexanderWhitneySummand_castSucc_D₂ (n : ℕ) (i : Fin (n + 1))
    (q : ℕ) (hq : n - (i : ℕ) = q) :
    alexanderWhitneySummand C D (n + 1) i.castSucc ≫
      mapBifunctor.D₂ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n =
    (-1 : ℤ) ^ (i : ℕ) •
      (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • awTensorTerm C D
        (awFront (n + 1) i.castSucc)
        (SimplexCategory.δ k ≫ awInterval i (q + 1) (n + 1) (by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega))
        (by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega)) := by
  have hq' : n + 1 - (i : ℕ) = q + 1 := by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega
  have he : alexanderWhitneySummand C D (n + 1) i.castSucc =
      awTensorTerm C D (awFront (n + 1) i.castSucc)
        (awInterval i (q + 1) (n + 1) (by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega))
        (by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega) := by
    change awTensorTerm C D (awFront (n + 1) i.castSucc)
      (awBack (n + 1) i.castSucc) (awDegrees (n + 1) i.castSucc) = _
    rw [awBack_eq_interval]
    exact awTensorTerm_interval_congr C D _ hq' _ _ _ _
  rw [he]
  exact awTensorTerm_D₂ C D _ _ (by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega)

/-- 概要：AW の垂直微分全体を最後以外の切断点の面の二重和へ展開する。
方針：最後の切断点の第二因子は零次なので垂直微分が零となる。
規約：KST Construction A.5、第一因子の次数の符号を保つ。
使われ方：垂直境界の非対角項と対角項の分離。 -/
lemma alexanderWhitney_vertical_boundary (n : ℕ) :
    alexanderWhitneyApp C D (n + 1) ≫
      mapBifunctor.D₂ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n =
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      (∑ k : Fin (n - (i : ℕ) + 2), (-1 : ℤ) ^ (k : ℕ) • awTensorTerm C D
        (awFront (n + 1) i.castSucc)
        (SimplexCategory.δ k ≫ awInterval i (n - (i : ℕ) + 1) (n + 1)
          (by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega)) (by have _hi : (i.castSucc : Fin (n + 2)).val = (i : ℕ) := rfl; have := i.isLt; omega)) := by
  rw [alexanderWhitneyApp, Preadditive.sum_comp, Fin.sum_univ_castSucc]
  have he : alexanderWhitneySummand C D (n + 1) (Fin.last (n + 1)) =
      awTensorTerm C D (awFront (n + 1) (Fin.last (n + 1)))
        (awInterval (n + 1) 0 (n + 1) (by omega)) (by simp) := by
    change awTensorTerm C D (awFront (n + 1) (Fin.last (n + 1)))
      (awBack (n + 1) (Fin.last (n + 1))) (awDegrees (n + 1) (Fin.last (n + 1))) = _
    rw [awBack_eq_interval]
    exact awTensorTerm_interval_congr C D _ (by simp) _ _ _ _
  rw [he, awTensorTerm_zero_D₂, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  exact alexanderWhitneySummand_castSucc_D₂ C D n i (n - (i : ℕ)) rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories


