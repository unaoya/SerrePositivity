module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalanceTerms

/-!
模型。文献の定義との比較は後で
# 全arityの元の合成切断と二段切断の対合

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §379。
空語・退化零項を含む元の全有限添字を、全係数環・単体に共通に対にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- L12a：全arityの元の全項の固定零項と反対符号の対合（BF §2.2.6）。 -/
lemma compositeBalance_pairing {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) :
    ∃ τ : Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBalanceIndex u v k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q (τ i) x = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm A S u v k q i x) := by
  cases n with
  | succ n =>
    refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm_involutive u v k q, ?_, ?_⟩
    · intro i hi
      exact False.elim (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm_ne u v k q i hi)
    · intro i _ A hA S x
      dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm]
      have h : -((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ) =
          -((d + e + q : ℕ) : ℤ) := by omega
      let f := eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (m + (n + 1))).X z) h)
      exact (congrArg (fun y => f y)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm_neg A S u v k q i x)).trans (map_neg f.hom _)
  | zero =>
    cases e with
    | succ e => exact isEmptyElim v
    | zero =>
      cases m with
      | succ m => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalance_pairing u v k
      | zero =>
        cases d with
        | succ d =>
          change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 1 (d + 1) at u
          exact isEmptyElim u
        | zero =>
          obtain ⟨τ, hτ, hfix, hneg⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryZeroBalance_pairing u v k q
          refine ⟨τ, hτ, ?_, ?_⟩
          · intro i hi A hA S x
            dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm]
            rw [hfix i hi A S x, map_zero]
          · intro i hi A hA S x
            dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeBalanceTerm]
            have h : -(q : ℤ) = -((0 + 0 + q : ℕ) : ℤ) := by omega
            let f := eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0).X z) h)
            exact (congrArg (fun y => f y) (hneg i hi A S x)).trans (map_neg f.hom _)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
