module

public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryInsertion

/-!
# 指定した入力次数で読む実際の空語代入の値

Berger–Fresse §2.2.6・§3.1、M14 L12a、報告 §344。
元の全次数を保持し、同じ前方・指定因子・後方の次数の和へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open IntervalCuts (prefixFamily suffixFamily insertionFamily)
open scoped Simplicial

/-- 同じ入力次数の等式移送だけで空語の元の値を読む（BF §2.2.6）。 -/
lemma tensorCoInsertionAction_cochain_nullary_positive_at (A : Type u) [CommRing A]
    (S : SSet.{0}) {m : ℕ} (v : Surjection.BasisWord 0 0) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (hpos : 0 < (f i).1) (p z : ℤ)
    (hp : -(vectorDegree (chains A S) (m + 1) f : ℤ) = p)
    (hz : 0 + p = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) m 0 i
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 1)) 0 p z hz
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f p hp)) = 0 := by
  have he : p = -(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ)) := by
    have hf := vectorDegree_family_blocks (chains A S) f i
    omega
  subst he
  exact tensorCoInsertionAction_cochain_nullary_positive A S v i f hpos z hz

/-- 同じ入力次数の等式移送だけで空語の元の値を読む（BF §2.2.6）。 -/
lemma tensorCoInsertionAction_cochain_nullary_zero_at (A : Type u) [CommRing A]
    (S : SSet.{0}) {m : ℕ} (v : Surjection.BasisWord 0 0) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (x : S _⦋0⦌) (hx : f i = ⟨0, gen A S 0 x⟩) (p z : ℤ)
    (hp : -(vectorDegree (chains A S) (m + 1) f : ℤ) = p)
    (hz : 0 + p = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) m 0 i
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 1)) 0 p z hz
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f p hp)) =
      vectorTensorAt (chains A S) (m + 0)
        (insertionFamily f (fun j : Fin 0 => Fin.elim0 j) i) z
        (by rw [vectorDegree_insertionFamily]
            have hi : (f i).1 = 0 := congrArg Sigma.fst hx
            change -(vectorDegree (chains A S) i.val (prefixFamily f i) + 0 +
              vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℕ) = z
            have hf := vectorDegree_family_blocks (chains A S) f i
            omega) := by
  have he : p = -(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ)) := by
    have hf := vectorDegree_family_blocks (chains A S) f i
    omega
  subst he
  exact tensorCoInsertionAction_cochain_nullary_zero A S v i f x hx z hz

end SerrePositivity.EInfinity.SimplexCuts
