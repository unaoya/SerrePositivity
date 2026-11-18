module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeSignedTermsAll

/-!
模型。文献の定義との比較は後で
# 正の全合成切断と二段切断の同じ有限対合

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

/-- 同じ二段切断の全次数を元の共通次数で読む（BF §2.2.6）。 -/
lemma positiveNested_degreeSum {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (m + (n + 1)) (fun a => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedFaceFamily u v k c a).1) =
      m + n + (d + e) + q + 1 - (m + (n + 1)) := by
  obtain ⟨b, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedEquiv u v k q).surjective c
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_nested_degreeSum u v k b

/-- 元の同値と逆を交換する、正の全添字の対合（BF §2.2.6）。 -/
def positiveCompositeBalancePerm {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q ⊕ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q) :=
  (Equiv.sumCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedEquiv u v k q)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedEquiv u v k q).symm).trans (Equiv.sumComm _ _)

/-- 同じ元の有限同値の往復で二回の交換は恒等（BF §2.2.6）。 -/
lemma positiveCompositeBalancePerm_involutive {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    Function.Involutive (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q) := by
  rintro (c | c) <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm]

/-- 交換する二つの枝は異なり、固定点はない（BF §2.2.6）。 -/
lemma positiveCompositeBalancePerm_ne {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q ⊕ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm u v k q i ≠ i := by
  cases i <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeBalancePerm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
