module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AlexanderWhitney
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerTensorAdditivity

/-!
概要：第二因子を零次へ写すと、AW の切断和では最後の切断だけが残る。
方針：全テンソル写像を各切断へ制限し、第二次数が正の項を消す。
規約：元の整数テンソルと指定 AW の射を保持する。
使われ方：HA 1.2.4、IS-W2 A05a の右増大写像計算、前提計算枠1。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))
variable {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}

/-- 第二因子の正次数を消す写像の後では、AW は最後の切断に一致する。 -/
theorem alexanderWhitneyApp_right_zero_degree
    (f : (alternatingFaceMapComplex _).obj C ⟶ K)
    (g : (alternatingFaceMapComplex _).obj D ⟶ L)
    (hg : ∀ k : ℕ, k ≠ 0 → g.f k = 0) (n : ℕ) :
    alexanderWhitneyApp C D n ≫ (chainIntegerTensorMap f g).f n =
      alexanderWhitneySummand C D n (Fin.last n) ≫ (chainIntegerTensorMap f g).f n := by
  rw [alexanderWhitneyApp, Preadditive.sum_comp]
  apply Finset.sum_eq_single (Fin.last n)
  · intro i _ hi
    have hdeg : n - (i : ℕ) ≠ 0 := by
      intro hz
      apply hi
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_last]
      omega
    dsimp only [alexanderWhitneySummand]
    rw [Category.assoc, ι_chainIntegerTensorMap, ← Category.assoc,
      ← integerTensorMap_comp, hg _ hdeg, CategoryTheory.Limits.comp_zero,
      integerTensorMap_zero_right, CategoryTheory.Limits.zero_comp]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
