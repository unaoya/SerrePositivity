module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalancePairing

/-!
模型。文献の定義との比較は後で
# 全arityの元の合成切断と二段切断の有限和

Berger–Fresse §1.2.4・§2.2.6、M14 L12、報告 §382。
同じ全対合と固定零項を使い、元の実テンソルで左右の和を比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 元の合成側と二段側の直和のどちらかを読むだけの記号（BF §2.2.6）。 -/
def compositeBalanceIsLeft : {m n d e : ℕ} →
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) → (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) →
    (k : Fin (m + 1)) → (q : ℕ) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalanceIndex u v k q → Bool
  | _, _ + 1, _, _, _, _, _, _, Sum.inl _ => true
  | _, _ + 1, _, _, _, _, _, _, Sum.inr _ => false
  | _, 0, _, _ + 1, _, _, _, _, i => PEmpty.elim i
  | _ + 1, 0, _, 0, _, _, _, _, Sum.inl _ => true
  | _ + 1, 0, _, 0, _, _, _, _, Sum.inr _ => false
  | 0, 0, _ + 1, 0, _, _, _, _, i => PEmpty.elim i
  | 0, 0, 0, 0, _, _, _, _, Sum.inl _ => true
  | 0, 0, 0, 0, _, _, _, _, Sum.inr _ => false

/-- 全arityの元の全有限項は固定零項を含め相殺する（BF §2.2.6）。 -/
lemma sum_compositeBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalanceIndex u v k q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x = 0 := by
  classical
  obtain ⟨τ, hτ, hfix, hneg⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalance_pairing u v k q
  apply Finset.sum_ninvolution τ
  · intro i
    by_cases hi : τ i = i
    · rw [hi, hfix i hi A S x, zero_add]
    · rw [hneg i hi A S x, add_neg_cancel]
  · intro i hne hi
    exact hne (hfix i hi A S x)
  · intro i
    exact Finset.mem_univ _
  · exact hτ

/-- 元の合成側の全項の和。二段側では零を補うだけ（BF §2.2.6）。 -/
def compositeCutSum (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) {q : ℕ} (x : S _⦋q⦌) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (m + n)).X (-((d + e + q : ℕ) : ℤ)) :=
  ∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalanceIndex u v k q,
    if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceIsLeft u v k q i then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x else 0

/-- 元の二段側の全項の和。合成側では零を補い負号を戻す（BF §2.2.6）。 -/
def nestedCutSum (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) {q : ℕ} (x : S _⦋q⦌) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (m + n)).X (-((d + e + q : ℕ) : ℤ)) :=
  ∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalanceIndex u v k q,
    if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceIsLeft u v k q i then 0 else -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x

/-- L12：元の合成Cut和と二段Cut和は全arityで一致する（BF §2.2.6）。 -/
lemma cutSum_composite (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeCutSum A S u v k x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nestedCutSum A S u v k x := by
  classical
  apply sub_eq_zero.mp
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeCutSum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nestedCutSum, ← Finset.sum_sub_distrib]
  have h (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalanceIndex u v k q) :
      (if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceIsLeft u v k q i then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x else 0) -
        (if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceIsLeft u v k q i then 0 else -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x) =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x := by
    split <;> simp
  simp_rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_compositeBalanceTerm_eq_zero A S u v k q x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
