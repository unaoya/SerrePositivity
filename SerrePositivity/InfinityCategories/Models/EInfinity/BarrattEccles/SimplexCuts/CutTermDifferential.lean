module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOutputFactor

/-!
模型。文献の定義との比較は後で
# 同じ切断項の微分と指定出力境界の全和

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の純粋テンソルの微分則を、零次数の因子も含む同じ実出力境界項へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C281：出力次数零の因子の同じテンソル微分の成分は零。 -/
lemma tensorValueDifferentialFactor_cut_zero (S : SSet.{0}) {m q r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r)
    (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a = 0) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v)
      (fun b => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v b) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v b).op x)) a = 0 := by
  have hg (p : ℕ) (hp : p = 0) (y : S _⦋p⦌) :
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d (-(p : ℤ)) (-(p : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S p y) = 0 := by
    subst p
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_d_zero A S y
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor_eq_zero_of_closed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v)
    (fun b => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v b) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v b).op x)) a
    (hg _ ha (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x))

/-- C257：同じ切断項の微分は、全指定出力面の同じ実境界値の和。 -/
lemma cutTerm_d_eq_sum_outputBoundaryTerm (S : SSet.{0})
    {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).d (-((m + q + 1 - r : ℕ) : ℤ))
        (-((m + q + 1 - r : ℕ) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S s v x) =
      ∑ a : Fin r, ∑ j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a + 1),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v a j x := by
  let K := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S
  let d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v
  have h0 : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) := by
    dsimp only [d]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum_eq_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_sum]
  have h1 : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d : ℤ) + 1 = -((m + q + 1 - r : ℕ) : ℤ) + 1 := by rw [h0]
  have hc : (power K r).d (-((m + q + 1 - r : ℕ) : ℤ))
      (-((m + q + 1 - r : ℕ) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S s v x) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v.val •
        (eqToHom (congrArg (fun z : ℤ => (power K r).X z) h1)).hom
          ((power K r).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d : ℤ) + 1)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor A S s v x)) := by
    have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.complex_d_cast_source_target A (power K r)
      (i := -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d : ℤ)) (i' := -((m + q + 1 - r : ℕ) : ℤ))
      (j := -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d : ℤ) + 1) (j' := -((m + q + 1 - r : ℕ) : ℤ) + 1)
      h0 h1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor A S s v x)
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensorAt]
    rw [map_zsmul]
    convert congrArg (fun y => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v.val • y) ht using 1
  rw [hc]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue_d_sum]
  simp only [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cast_tensorValueDifferentialFactor_eq_sum_deletedCutTensor A S s v a ha x h1]
    simp only [Finset.smul_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm, dite_eq_left ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySign, mul_smul]
  · have hz : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a = 0 := by omega
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor_cut_zero A S s v a hz x, map_zero, smul_zero]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm, dite_eq_right ha, Finset.sum_const_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
