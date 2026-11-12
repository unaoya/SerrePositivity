module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiTerminalCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarColumnAction

/-!
概要：bar の Bianchi データの全体 HA 右辺を、元の内部頂点にわたる和へ直す。
方針：全頂点の和の両端の零を除き、元の非初期頂点で添字付ける。
規約：HA の元の符号・係数と端点をそのまま保持する。
使われ方：θ の面・prefix の一次和との一項ごとの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))


lemma dgCoherentBar_withLast_univ (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (Finset.univ : Finset (Fin (n + 1))) =
      (Finset.univ : Finset (Fin (n + 2))) := by
  ext x
  induction x using Fin.lastCases with
  | last => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]
  | cast x => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]

def dgCoherentBarBianchiFullTerm {n : ℕ} (σ : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    GradedHom R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 2)))
      (-((n + 1 : ℕ) : ℤ) + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).term Finset.univ 0 (Fin.last (n + 2))
    (-((n + 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + 1)) (by simp; omega)
    i.succ.castSucc (Finset.mem_univ _)
    (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i)) (Fin.castSucc_lt_last _)

lemma dgCoherentBarBianchiData_full_rhs_sum {n : ℕ} (σ : I _⦋n + 1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).rhs Finset.univ 0 (Fin.last (n + 2))
      (-((n + 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + 1)) (by simp; omega) =
      ∑ i : Fin (n + 1), dgCoherentBarBianchiFullTerm R D F σ i := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ, Fin.sum_univ_castSucc]
  simp only [lt_self_iff_false, and_false, dite_false, add_zero]
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, lt_self_iff_false, false_and, dite_false, zero_add,
    Fin.castSucc_lt_last, and_true, dgCoherentBarBianchiFullTerm]
  apply Finset.sum_congr rfl
  intro i _
  rw [dite_eq_left (show (0 : Fin (n + 3)) < i.succ.castSucc from
    Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i))]


lemma dgCoherentBarBianchiFullTerm_sign (n : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (Finset.univ : Finset (Fin (n + 3))) i.succ.castSucc =
      ((n : ℤ) + 1 - (i.val : ℤ)).negOnePow := by
  have hf : (Finset.univ : Finset (Fin (n + 3))).filter (i.succ.castSucc < ·) =
      Finset.univ.filter (i.succ.succ ≤ ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.castSucc_lt_iff_succ_le
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign
  rw [hf, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail_card]
  congr 1
  have hi : i.val < n + 1 := i.isLt
  simp only [Fin.val_succ]
  omega

end SerrePositivity.InfinityCategories.Project.DerivedCategories
