module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeBalanceTerms

/-!
模型。文献の定義との比較は後で
# 正の全合成切断項と二段切断項の有限和の相殺

Berger–Fresse §2.2.6、M14 L12a の正の枝、報告 §304。
同じ全有限添字・整数係数・元の生成元の値を保つ。nullaryは別に残す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 同じ対応で読む元の全項は、退化零項を含め符号で相殺する（BF §2.2.6）。 -/
lemma positiveCompositeBalancePerm_neg (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q ⊕ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalanceTerm A S u v k q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q i) x =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalanceTerm A S u v k q i x := by
  have hf (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) :
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalanceTerm A S u v k q
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q (Sum.inl c)) x =
        -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalanceTerm A S u v k q (Sum.inl c) x := by
    have h := congrArg (fun z => -z)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_signedCutTerm_eq_nested_all A S u v k c x).symm
    simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalanceTerm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedEquiv] using h
  cases i with
  | inl c => exact hf c
  | inr c =>
    let b := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedEquiv u v k q).symm c
    have hm : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q (Sum.inl b) = Sum.inr c := by
      simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm, b]
    have hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q (Sum.inr c) = Sum.inl b := by
      rw [← hm]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm_involutive u v k q _
    have h := hf b
    rw [hm] at h
    rw [hb]
    simpa only [neg_neg] using (congrArg (fun z => -z) h).symm

/-- 同じ正の全添字の実テンソルの有限和は零（BF §2.2.6）。 -/
lemma sum_positiveCompositeBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q ⊕ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalanceTerm A S u v k q i x = 0 := by
  classical
  apply Finset.sum_ninvolution (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q)
  · intro i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm_neg A S u v k q i x]
    exact add_neg_cancel _
  · intro i _ he
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm_ne u v k q i) he
  · intro i
    exact Finset.mem_univ _
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm_involutive u v k q

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
