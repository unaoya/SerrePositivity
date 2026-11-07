module

public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion
public import Mathlib.RingTheory.Derivation.Lie

/-!
# 完備多項式の偏微分

## 概要
多項式の偏微分を p 完備多項式環に延長する。

## 方針
完備化の列による表示で各係数を微分する。微分は p 倍と右シフトに可換。

## 規約
微分は元の係数環上の線形写像。

## 使われ方
完備 de Rham 複体の微分。
-/

public section
noncomputable section

universe u

open SerrePositivity.DerivedCompletion

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ)

local notation "P" => Poly k T
local notation "Q" => completedPoly k T p
local notation "L" => PrincipalReflectionModule P (p : P)
local notation "N" => LinearMap.range (principalReflectionRelation P (p : P))

private def onSequences (f : P →ₗ[k] P) : (ℕ → P) →ₗ[k] (ℕ → P) :=
  LinearMap.pi fun n => f.comp (LinearMap.proj n)

omit [Fintype T] [DecidableEq T] in
private theorem onSequences_relation (f : P →ₗ[k] P) (x : ℕ → P) :
    onSequences k T f (principalReflectionRelation P (p : P) x) =
      principalReflectionRelation P (p : P) (onSequences k T f x) := by
  funext n
  change f (sequenceShiftRight P x n - (p : P) * x n) =
    sequenceShiftRight P (onSequences k T f x) n - (p : P) * f (x n)
  rw [map_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]
  congr 1
  cases n
  · exact map_zero f
  · rfl

private def reflectionMap (f : P →ₗ[k] P) : L →ₗ[k] L :=
  (Submodule.restrictScalars k N).liftQ ((principalReflectionMk P (p : P)).restrictScalars k ∘ₗ
    onSequences k T f) (by
      rintro _ ⟨x, rfl⟩
      change principalReflectionMk P (p : P)
        (onSequences k T f (principalReflectionRelation P (p : P) x)) = 0
      rw [onSequences_relation]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩)

omit [Fintype T] [DecidableEq T] in
private theorem reflectionMap_mk (f : P →ₗ[k] P) (x : ℕ → P) :
    reflectionMap k T p f (principalReflectionMk P (p : P) x) =
      principalReflectionMk P (p : P) (onSequences k T f x) := by
  unfold reflectionMap
  rfl

private def completeLinearMap (f : P →ₗ[k] P) : Q →ₗ[k] Q :=
  let e := (principalCompletionH0Equiv P (p : P)).restrictScalars k
  e.symm.toLinearMap ∘ₗ reflectionMap k T p f ∘ₗ e.toLinearMap

private theorem completeLinearMap_unit (f : P →ₗ[k] P) (x : P) :
    completeLinearMap k T p f (algebraMap P Q x) = algebraMap P Q (f x) := by
  apply (principalCompletionH0Equiv P (p : P)).injective
  change (principalCompletionH0Equiv P (p : P))
    ((principalCompletionH0Equiv P (p : P)).symm
      (reflectionMap k T p f ((principalCompletionH0Equiv P (p : P))
        (principalCompletionUnitRingHom P (p : P) x)))) =
    (principalCompletionH0Equiv P (p : P)) (principalCompletionUnitRingHom P (p : P) (f x))
  rw [LinearEquiv.apply_symm_apply]
  simp only [principalCompletionUnitRingHom_apply, principalCompletionH0Equiv_unit,
    reflectionMap_mk]
  congr 1
  funext n
  cases n
  · rfl
  · exact map_zero f

private theorem completeLinearMap_comp_apply (f g : P →ₗ[k] P) (x : Q) :
    completeLinearMap k T p f (completeLinearMap k T p g x) =
      completeLinearMap k T p (f.comp g) x := by
  let e := principalCompletionH0Equiv P (p : P)
  let q := principalReflectionMk P (p : P)
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective N (e x)
  have hx : x = e.symm (q z) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact hz.symm
  rw [hx]
  change e.symm (reflectionMap k T p f (e (e.symm (reflectionMap k T p g (e (e.symm (q z))))))) =
    e.symm (reflectionMap k T p (f.comp g) (e (e.symm (q z))))
  simp only [LinearEquiv.apply_symm_apply]
  rfl

/-- 概要：完備多項式環上の偏微分。
方針：列の表示で元の多項式偏微分を項ごとに適用する。
規約：元の係数環上で線形。
使われ方：完備 de Rham 複体の微分。 -/
def completedPderiv (t : T) : Q →ₗ[k] Q :=
  completeLinearMap k T p (MvPolynomial.pderiv t).toLinearMap

/-- 完備化単位は多項式の偏微分とその延長を比較する。 -/
theorem completedPderiv_unit (t : T) (x : P) :
    completedPderiv k T p t (algebraMap P Q x) =
      algebraMap P Q (MvPolynomial.pderiv t x) :=
  completeLinearMap_unit k T p _ x

/-- 完備多項式の二つの偏微分は可換。 -/
theorem completedPderiv_comm (s t : T) (x : Q) :
    completedPderiv k T p s (completedPderiv k T p t x) =
      completedPderiv k T p t (completedPderiv k T p s x) := by
  have h : ⁅MvPolynomial.pderiv (R := k) s, MvPolynomial.pderiv (R := k) t⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply]
    split <;> split <;> simp
  have hf : (MvPolynomial.pderiv (R := k) s).toLinearMap.comp
      (MvPolynomial.pderiv t).toLinearMap =
      (MvPolynomial.pderiv t).toLinearMap.comp (MvPolynomial.pderiv s).toLinearMap := by
    apply LinearMap.ext
    intro y
    change MvPolynomial.pderiv s (MvPolynomial.pderiv t y) =
      MvPolynomial.pderiv t (MvPolynomial.pderiv s y)
    exact sub_eq_zero.mp (by
      simpa only [Derivation.commutator_apply, Derivation.zero_apply] using
        congrArg (fun D : Derivation k P P => D y) h)
  unfold completedPderiv
  rw [completeLinearMap_comp_apply, completeLinearMap_comp_apply, hf]

end SerrePositivity.DeRham
