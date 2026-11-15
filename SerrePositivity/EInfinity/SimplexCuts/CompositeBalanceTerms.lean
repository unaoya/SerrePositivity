module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveCompositeBalanceCancellation
public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroBalancePairing

/-!
# 全arityの元の合成切断と二段切断の有限項

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §379。
元の全有限添字・整数係数・指定面を共通次数へ包装する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 全arityの元の合成側と二段側の有限添字（BF §2.2.6）。 -/
def CompositeBalanceIndex : {m n d e : ℕ} →
    (u : Surjection.BasisWord (m + 1) d) → (v : Surjection.BasisWord n e) →
    Fin (m + 1) → ℕ → Type
  | _, _ + 1, _, _, u, v, k, q =>
      PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q
  | _, 0, _, _ + 1, _, _, _, _ => PEmpty
  | m + 1, 0, _, 0, u, _, k, q => NullaryNativeBalanceIndex (m := m) u k q
  | 0, 0, _ + 1, 0, _, _, _, _ => PEmpty
  | 0, 0, 0, 0, u, _, k, q => NullaryZeroBalanceIndex u k q

/-- 元の全有限添字の有限性を保つ包装（BF §2.2.6）。 -/
instance compositeBalanceIndexFintype {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (q : ℕ) : Fintype (CompositeBalanceIndex u v k q) := by
  cases n with
  | succ n => exact inferInstanceAs (Fintype (PositiveCompositeCutIndex u v k q ⊕
      PositiveNestedCutIndex u v k q))
  | zero =>
    cases e with
    | succ e => exact inferInstanceAs (Fintype PEmpty)
    | zero =>
      cases m with
      | succ m => exact inferInstanceAs (Fintype (NullaryNativeBalanceIndex u k q))
      | zero =>
        cases d with
        | succ d => exact inferInstanceAs (Fintype PEmpty)
        | zero => exact inferInstanceAs (Fintype (NullaryZeroBalanceIndex u k q))

/-- 元の全有限項を同じ整数次数へ移すだけの包装（BF §2.2.6）。 -/
def compositeBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0}) :
    {m n d e : ℕ} → (u : Surjection.BasisWord (m + 1) d) → (v : Surjection.BasisWord n e) →
    (k : Fin (m + 1)) → (q : ℕ) → CompositeBalanceIndex u v k q → S _⦋q⦌ →
      (power (chains A S) (m + n)).X (-((d + e + q : ℕ) : ℤ))
  | m, n + 1, d, e, u, v, k, q, i, x =>
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (m + (n + 1))).X z)
        (by omega : -((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ) =
          -((d + e + q : ℕ) : ℤ))))
        (positiveCompositeBalanceTerm A S u v k q i x)
  | _, 0, _, _ + 1, _, _, _, _, i, _ => PEmpty.elim i
  | _ + 1, 0, _, 0, u, v, k, q, i, x => nullaryNativeBalanceTerm A S u v k q i x
  | 0, 0, _ + 1, 0, _, _, _, _, i, _ => PEmpty.elim i
  | 0, 0, 0, 0, u, v, k, q, i, x =>
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) 0).X z)
        (by omega : -(q : ℤ) = -((0 + 0 + q : ℕ) : ℤ))))
        (nullaryZeroBalanceTerm A S u v k q i x)

end SerrePositivity.EInfinity.SimplexCuts
