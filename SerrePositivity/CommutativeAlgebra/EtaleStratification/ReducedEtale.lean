module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# 被約基底上の有限エタール代数

## 概要
被約環上の有限エタール代数は被約である。

## 方針
有限エタール代数は有限表示平坦加群なので射影的。
自由加群への分裂単射の各座標を剰余体へ移し、被約なファイバーで冪零元が消えることを使う。

## 規約
基底の noetherian 性は仮定しない。

## 使われ方
近似環から元の環へ底変換した後、被約化を伴う層の有限エタール部分を保つ。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 射影的な代数の全剰余体ファイバーが被約なら、被約基底上で代数も被約。 -/
theorem isReduced_of_projective_of_reduced_fibers
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsReduced R] [Module.Projective R A]
    (hfibers : ∀ (P : Ideal R) [P.IsPrime], IsReduced (P.ResidueField ⊗[R] A)) :
    IsReduced A := by
  constructor
  intro x hx
  have hcoord (φ : A →ₗ[R] R) : φ x = 0 := by
    apply IsNilpotent.eq_zero
    apply nilpotent_iff_mem_prime.mpr
    intro P hP
    let : P.IsPrime := hP
    let K := P.ResidueField
    let : IsReduced (K ⊗[R] A) := hfibers P
    have hzero : (1 : K) ⊗ₜ[R] x = 0 :=
      (hx.map (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)).eq_zero
    have he := congrArg (fun t ↦ TensorProduct.rid R K (φ.lTensor K t)) hzero
    apply (Ideal.algebraMap_residueField_eq_zero (I := P)).mp
    simpa [Algebra.smul_def] using he
  obtain ⟨s, hs⟩ := (Module.projective_def (R := R) (P := A)).mp inferInstance
  apply hs.injective
  ext a
  simpa using hcoord ((Finsupp.lapply a).comp s)

/-- 有限エタール代数は、被約基底上では被約。 -/
theorem isReduced_of_finite_etale (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [IsReduced R]
    [Module.Finite R A] [Algebra.Etale R A] : IsReduced A := by
  let : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation
  let : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  apply isReduced_of_projective_of_reduced_fibers R A
  intro P _
  exact Algebra.FormallyUnramified.isReduced_of_field P.ResidueField (P.ResidueField ⊗[R] A)

end SerrePositivity.CommutativeAlgebra
