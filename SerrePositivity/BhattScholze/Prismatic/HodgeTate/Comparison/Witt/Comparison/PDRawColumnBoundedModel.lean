module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Category.ModuleCat.Projective
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn

/-!
# 第 0 分冪 de Rham 列の有界射影模型

## 概要
未完備の第 0 列は、変数の数を上限とする自由な複体である。

## 方針
外冪の消滅を使って有界性を示し、各自由加群の射影性を整数添字への延長に移す。

## 規約
負次数は零で補う。

## 使われ方
BS 著者版 Theorem 6.4 の第 0 列の導来底変換を通常のテンソル積で計算する。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [CommRing k] (r : ℕ)

local notation "K" => pdUncompletedColumn k r ⦋0⦌
local notation "e" => ComplexShape.embeddingUpNat

private theorem raw_isZero (j : ℕ) (h : r < j) : IsZero ((K).X j) := by
  let b : Module.Basis (Fin r × Fin (0 + 1)) k ((Fin r × Fin (0 + 1)) →₀ k) :=
    Finsupp.basisSingleOne
  let : Subsingleton (⋀[k]^j ((Fin r × Fin (0 + 1)) →₀ k)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt b b.span_eq j
      (by simpa [Nat.card_eq_fintype_card, Fintype.card_prod] using h)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hzero (x : (K).X j) : x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul a w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- 整数添字で読んだ未完備第 0 列は、変数の数を上限とする。 -/
theorem pdUncompletedColumnZero_isStrictlyLE :
    CochainComplex.IsStrictlyLE ((K).extend e) (r : ℤ) := by
  apply (CochainComplex.isStrictlyLE_iff _ _).mpr
  intro i hi
  by_cases h : ∃ j, (e).f j = i
  · obtain ⟨j,rfl⟩ := h
    have hj : r < j := by
      change (r : ℤ) < (j : ℤ) at hi
      exact_mod_cast hi
    exact (raw_isZero k r j hj).of_iso ((K).extendXIso e rfl)
  · exact (K).isZero_extend_X e i (fun j hj => h ⟨j,hj⟩)

/-- 未完備第 0 列の各項は射影的。 -/
theorem pdUncompletedColumnZero_projective (i : ℤ) : Projective (((K).extend e).X i) := by
  by_cases h : ∃ j, (e).f j = i
  · obtain ⟨j,rfl⟩ := h
    let : Module.Free k ((K).X j) := pdRawForms_free k r ⦋0⦌ j
    have hp : Projective ((K).X j) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis k ((K).X j))
    exact Projective.of_iso ((K).extendXIso e rfl).symm hp
  · exact ((K).isZero_extend_X e i (fun j hj => h ⟨j,hj⟩)).projective

/-- 第 0 列のもとの自由複体を、そのまま導来底変換の射影模型として使う。 -/
def pdUncompletedColumnZeroModel :
    BoundedAboveDerivedModel (DerivedCategory.Q.obj ((K).extend e)) where
  complex := (K).extend e
  bound := r
  bounded := pdUncompletedColumnZero_isStrictlyLE k r
  projective := pdUncompletedColumnZero_projective k r
  iso := Iso.refl _

end SerrePositivity.BhattScholze.Prismatic
