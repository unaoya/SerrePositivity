module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTateComplex

/-!
# 巡回群の両側周期複体の完全性

DAG XIII Construction 2.2.6 の Tate 経路の鎖レベルの補助。
左正則表現のノルムと作用差について、既存の二つの像・核の等式を
同じ整数全次数の周期複体へ適用する。スペクトル的な Tate 比較は別に行う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable (k : Type u) [CommRing k] {G : Type u} [CommGroup G] [Fintype G]

/-- 生成元を指定した左正則周期複体は整数全次数で完全。 -/
lemma cyclicTateComplex_leftRegular_exactAt (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℤ) :
    (cyclicTateComplex (Rep.leftRegular k G) g).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  have hm : i - 1 + 1 = i := by omega
  by_cases hi : Even i
  · have hp : ¬Even (i - 1) := by
      intro h
      exact Int.not_even_iff_odd.mpr (by simpa using h.add_one) hi
    simpa [cyclicTateComplex, CochainComplex.of.d, hm, cyclicTateDifferential, hi, hp]
      using Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub k g hg
  · have hp : Even (i - 1) := by
      have h := (Int.not_even_iff_odd.mp hi).sub_odd (show Odd (1 : ℤ) by decide)
      exact h
    simpa [cyclicTateComplex, CochainComplex.of.d, hm, cyclicTateDifferential, hi, hp]
      using Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_norm k g hg

/-- 各次数の左正則項は射影的。 -/
lemma cyclicTateComplex_leftRegular_projective (g : G) (i : ℤ) :
    Projective ((cyclicTateComplex (Rep.leftRegular k G) g).X i) :=
  inferInstanceAs (Projective (Rep.leftRegular k G))

end SerrePositivity.EInfinity.PowerOperation
