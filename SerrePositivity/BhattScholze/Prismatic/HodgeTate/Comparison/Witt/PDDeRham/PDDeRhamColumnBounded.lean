module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePower
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 完備分冪 de Rham 列の有界性と完備性

## 概要
各列は頂点の変数の個数より高い次数で消え、各項は p 完備である。

## 方針
頂点の微分形式の基底から外冪の有限自由性を得る。
有限自由加群をテンソルしても主元完備性は保たれる。

## 規約
添字は余単体次数と de Rham 次数。

## 使われ方
BS 著者版 Theorem 6.4 の Witt の比較で、有限枠の第 0 列を有界な完備模型として使う。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k] (r n j : ℕ)

local notation "T" => pdTerm p k r n
local notation "M" => ((Fin r × Fin (n + 1)) →₀ k)
local notation "E" => (⋀[k]^j M)

/-- 頂点の変数の個数を越える de Rham 次数は零。 -/
theorem pdDeRhamColumn_isZero_of_lt (h : r * (n + 1) < j) :
    IsZero ((pdDeRhamColumn p k r ⦋n⦌).X j) := by
  let b : Module.Basis (Fin r × Fin (n + 1)) k M := Finsupp.basisSingleOne
  let : Subsingleton E := exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    b b.span_eq j (by simpa [Nat.card_eq_fintype_card, Fintype.card_prod] using h)
  change IsZero (ModuleCat.of k (T ⊗[k] E))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hzero (x : T ⊗[k] E) : x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul a w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
    | add a w ha hw => rw [ha, hw, add_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- 各列の各項は基底上の p 完備加群。 -/
theorem pdDeRhamColumn_isModuleComplete :
    IsModuleComplete k (p : k) ((pdDeRhamColumn p k r ⦋n⦌).X j) := by
  classical
  let b : Module.Basis (Fin r × Fin (n + 1)) k M := Finsupp.basisSingleOne
  let e := Fintype.equivFin (Fin r × Fin (n + 1))
  let : LinearOrder (Fin r × Fin (n + 1)) := LinearOrder.lift' e e.injective
  let c := b.exteriorPower j
  let : Module.Free k E := Module.Free.of_basis c
  let : Module.Finite k E := Module.Finite.of_basis c
  change IsModuleComplete k (p : k) (ModuleCat.of k (T ⊗[k] E))
  exact isModuleComplete_tensor_finite_free k (p : k) (ModuleCat.of k T) (ModuleCat.of k E)
    (completedRing_isModuleComplete k p)

/-- 自然数添字から整数添字に延長した第 0 列は、変数の数を上限とする。 -/
theorem pdDeRhamColumnZero_isStrictlyLE :
    CochainComplex.IsStrictlyLE
      ((pdDeRhamColumn p k r ⦋0⦌).extend ComplexShape.embeddingUpNat) (r : ℤ) := by
  let K := pdDeRhamColumn p k r ⦋0⦌
  let e := ComplexShape.embeddingUpNat
  apply (CochainComplex.isStrictlyLE_iff _ _).mpr
  intro i hi
  by_cases h : ∃ j, e.f j = i
  · obtain ⟨j, rfl⟩ := h
    have hj : r < j := by
      change (r : ℤ) < (j : ℤ) at hi
      exact_mod_cast hi
    exact (pdDeRhamColumn_isZero_of_lt p k r 0 j (by simpa using hj)).of_iso
      (K.extendXIso e rfl)
  · exact K.isZero_extend_X e i (fun j hj => h ⟨j, hj⟩)

/-- 整数添字で読んだ完備分冪 de Rham 列は導来 p 完備。 -/
theorem pdDeRhamColumn_isComplete :
    DerivedCompletion.IsComplete k (p : k)
      (DerivedCategory.Q.obj ((pdDeRhamColumn p k r ⦋n⦌).extend ComplexShape.embeddingUpNat)) := by
  let K := pdDeRhamColumn p k r ⦋n⦌
  let e := ComplexShape.embeddingUpNat
  apply isComplete_Q_of_terms k (p : k)
  intro i
  by_cases h : ∃ j, e.f j = i
  · obtain ⟨j, rfl⟩ := h
    exact isModuleComplete_of_linearEquiv k (p : k) _ _
      (K.extendXIso e rfl).symm.toLinearEquiv (pdDeRhamColumn_isModuleComplete p k r n j)
  · have hz := K.isZero_extend_X e i (fun j hj => h ⟨j, hj⟩)
    let : Subsingleton ((K.extend e).X i) := ModuleCat.isZero_iff_subsingleton.mp hz
    exact isModuleComplete_of_pow_smul_zero k (p : k) _ 0 (fun _ => Subsingleton.elim _ _)

end SerrePositivity.BhattScholze.Prismatic
