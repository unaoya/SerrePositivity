module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Data.Int.Interval
public import SerrePositivity.HomologicalAlgebra.FiniteSupportCoproduct
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # cochain 複体のテンソル積の上下の限界と有限な次数

## 概要

cochain 複体のテンソル積の下限と上限を、因子それぞれの下限・上限から別々に与え、有界な複体のテンソル積の各次数が有限個の項の直和であることを示す。

## 方針

限界は Mathlib の `CochainComplex.IsStrictlyGE`・`IsStrictlyLE` で述べ、各次数の和因子を有限集合で数える。

## 規約

Mathlib の CochainComplex の埋め込みと切り詰め（`Mathlib.Algebra.Homology.Embedding.CochainComplex`）を import するので `CochainTensor/Basic` と分ける。Basic に入れると、Basic だけを使うファイルで `K.ιTruncLE` などのドット記法の解決が変わる。

## 使われ方

PerfectComplex のテンソル（完全性・台）、KTheory/Adams、BS の導来テンソル（`cochainTensor_isStrictlyLE`）。
-/

@[expose] public noncomputable section

universe u

section CochainTensorBoundsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A tensor summand is zero when its left factor is zero. -/
lemma cochainTensorSummand_isZero_left (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) (h : IsZero (P.X ij.val.1)) :
    IsZero (cochainTensorSummand P Q n ij) := by
  exact (tensorRight (Q.X ij.val.2)).map_isZero h

/-- A degree vanishes when each homogeneous summand has a zero factor. -/
lemma cochainTensor_isZero_X_of_summands
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (h : ∀ i j : ℤ, i + j = n → IsZero (P.X i) ∨ IsZero (Q.X j)) :
    IsZero ((cochainTensor P Q).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j hij
  rcases h i j hij with hi | hj
  · exact ((tensorRight (Q.X j)).map_isZero hi).eq_of_src _ _
  · exact ((tensorLeft (P.X i)).map_isZero hj).eq_of_src _ _

/-- Upper bounds add without imposing any lower bounds. -/
lemma cochainTensor_isStrictlyLE
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] : (cochainTensor P Q).IsStrictlyLE (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  apply cochainTensor_isZero_X_of_summands
  intro i j hij
  by_cases hi : a < i
  · exact Or.inl (P.isZero_of_isStrictlyLE a i hi)
  · exact Or.inr (Q.isZero_of_isStrictlyLE b j (by omega))

/-- Lower bounds add without imposing any upper bounds. -/
lemma cochainTensor_isStrictlyGE
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [Q.IsStrictlyGE b] : (cochainTensor P Q).IsStrictlyGE (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  apply cochainTensor_isZero_X_of_summands
  intro i j hij
  by_cases hi : i < a
  · exact Or.inl (P.isZero_of_isStrictlyGE a i hi)
  · exact Or.inr (Q.isZero_of_isStrictlyGE b j (by omega))

end SerrePositivity

end CochainTensorBoundsPart

section CochainTensorFinitePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory
variable {R : Type u} [CommRing R]

/-- Boundedness leaves only finitely many nonzero summands in each total degree. -/
lemma cochainTensorSummands_finiteSupport (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hb : ∀ i, i < a ∨ b < i → IsZero (P.X i)) (n : ℤ) :
    ∃ s : Finset {ij : ℤ × ℤ // ij.1 + ij.2 = n},
      ∀ ij, ij ∉ s → IsZero (cochainTensorSummand P Q n ij) := by
  classical
  let I := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let e : {i // i ∈ Finset.Icc a b} ↪ I :=
    ⟨fun i => ⟨(i.val, n - i.val), by omega⟩,
      fun i j h => Subtype.ext (congrArg (fun t : I => t.val.1) h)⟩
  let s := (Finset.Icc a b).attach.map e
  have hzero : ∀ ij : I, ij ∉ s → IsZero (cochainTensorSummand P Q n ij) := by
    intro ij hi
    apply cochainTensorSummand_isZero_left
    apply hb
    by_contra hh
    have hiab : ij.val.1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr (by omega)
    apply hi
    apply Finset.mem_map.mpr
    refine ⟨⟨ij.val.1, hiab⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    dsimp [e]
    apply Prod.ext
    · rfl
    · have := ij.property
      omega
  exact ⟨s, hzero⟩

/-- Each tensor degree is finite when the first complex is bounded and both have finite terms. -/
lemma cochainTensor_finite_X (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, Module.Finite R (P.X i)) (hq : ∀ j, Module.Finite R (Q.X j))
    (a b : ℤ) (hb : ∀ i, i < a ∨ b < i → IsZero (P.X i)) (n : ℤ) :
    Module.Finite R ((cochainTensor P Q).X n) := by
  classical
  obtain ⟨s, hs⟩ := cochainTensorSummands_finiteSupport P Q a b hb n
  have hS : ∀ ij, Module.Finite R (cochainTensorSummand P Q n ij) := by
    intro ij
    have := hp ij.val.1
    have := hq ij.val.2
    change Module.Finite R (TensorProduct R (P.X ij.val.1) (Q.X ij.val.2))
    infer_instance
  have : Module.Finite R (∐ cochainTensorSummand P Q n : ModuleCat.{u} R) :=
    moduleFinite_coproduct_of_finiteSupport _ s hs
  let E := (cochainTensorXIso P Q n).toLinearEquiv
  exact Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective

end SerrePositivity

end CochainTensorFinitePart
