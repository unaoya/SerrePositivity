module

public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import all SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion

/-!
# 多項式 de Rham 複体の完備化単位

## 概要
未完備形式の完備化単位を余鎖写像としてまとめる。
未完備複体は各項が自由で、変数の個数を上限とする。

## 方針
次数ごとにテンソルの係数を 1 とする写像を用い、微分との可換性は既存の公式で確認する。

## 規約
変数型は有限。整数添字の複体へは負次数を零として延長する。

## 使われ方
BS 著者版 Theorem 6.4 の de Rham の導来完備底変換。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ)

private def formsCompletionLinear (j : ℕ) : forms k T j →ₗ[k] completedForms k T p j :=
  (TensorProduct.mk (Poly k T) (completedPoly k T p) (forms k T j) 1).restrictScalars k

/-- 多項式 de Rham 複体から完備複体への標準写像。 -/
def deRhamCompletionUnit : deRhamComplex k T ⟶ completedDeRhamComplex k T p :=
  CochainComplex.ofHom (fun j => ModuleCat.ofHom (formsCompletionLinear k T p j)) (by
    intro j
    apply ModuleCat.hom_ext
    ext x
    dsimp only [completedDeRhamComplex, deRhamComplex] at *
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact completedDeRhamD_unit k T p j x)

/-- 未完備の多項式微分形式は係数環上の自由加群。 -/
theorem forms_free [LinearOrder T] (j : ℕ) : Module.Free k (forms k T j) := by
  let : Module.Free k (⋀[k]^j (T → k)) := Module.Free.of_basis ((Pi.basisFun k T).exteriorPower j)
  change Module.Free k (MvPolynomial T k ⊗[k] (⋀[k]^j (T → k)))
  infer_instance

/-- 変数の数を越える次数では多項式微分形式は零。 -/
theorem forms_isZero_of_card_lt (j : ℕ) (h : Fintype.card T < j) :
    IsZero (ModuleCat.of k (forms k T j)) := by
  let b := Pi.basisFun k T
  let : Subsingleton (⋀[k]^j (T → k)) := exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    b b.span_eq j (by simpa [Nat.card_eq_fintype_card] using h)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hzero (x : forms k T j) : x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul a v => rw [Subsingleton.elim v 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- 整数添字の未完備 de Rham 複体は変数の個数を上限とする。 -/
theorem deRhamComplex_isStrictlyLE :
    CochainComplex.IsStrictlyLE ((deRhamComplex k T).extend ComplexShape.embeddingUpNat)
      (Fintype.card T : ℤ) := by
  let K := deRhamComplex k T
  let e := ComplexShape.embeddingUpNat
  apply (CochainComplex.isStrictlyLE_iff _ _).mpr
  intro i hi
  by_cases h : ∃ j, e.f j = i
  · obtain ⟨j, rfl⟩ := h
    have hj : Fintype.card T < j := by
      change (Fintype.card T : ℤ) < (j : ℤ) at hi
      exact_mod_cast hi
    exact (forms_isZero_of_card_lt k T j hj).of_iso (K.extendXIso e rfl)
  · exact K.isZero_extend_X e i (fun j hj => h ⟨j, hj⟩)

end SerrePositivity.DeRham
