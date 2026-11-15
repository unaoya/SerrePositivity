module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSignedTermsAll

/-!
# 正の全合成切断と二段切断の同じ有限対合

Berger–Fresse §2.2.6、M14 L12a の正の枝、報告 §304。
同じ全有限添字・整数係数・元の生成元の値を保つ。nullaryは別に残す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial

/-- 同じ二段切断の全次数を元の共通次数で読む（BF §2.2.6）。 -/
lemma positiveNested_degreeSum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    degreeSum (m + (n + 1)) (fun a => (positiveNestedFaceFamily u v k c a).1) =
      m + n + (d + e) + q + 1 - (m + (n + 1)) := by
  obtain ⟨b, rfl⟩ := (positiveCompositeNestedEquiv u v k q).surjective c
  exact positiveComposite_nested_degreeSum u v k b

/-- 元の同値と逆を交換する、正の全添字の対合（BF §2.2.6）。 -/
def positiveCompositeBalancePerm {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    Equiv.Perm (PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q) :=
  (Equiv.sumCongr (positiveCompositeNestedEquiv u v k q)
    (positiveCompositeNestedEquiv u v k q).symm).trans (Equiv.sumComm _ _)

/-- 同じ元の有限同値の往復で二回の交換は恒等（BF §2.2.6）。 -/
lemma positiveCompositeBalancePerm_involutive {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    Function.Involutive (positiveCompositeBalancePerm u v k q) := by
  rintro (c | c) <;> simp [positiveCompositeBalancePerm]

/-- 交換する二つの枝は異なり、固定点はない（BF §2.2.6）。 -/
lemma positiveCompositeBalancePerm_ne {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ)
    (i : PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q) :
    positiveCompositeBalancePerm u v k q i ≠ i := by
  cases i <;> simp [positiveCompositeBalancePerm]

end SerrePositivity.EInfinity.SimplexCuts
