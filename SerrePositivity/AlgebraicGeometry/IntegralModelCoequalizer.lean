module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Span.Basic

/-!
概要：有限・有限表示の模型の平行射を、有限生成イデアルによる商で等しくする。
方針：始域の有限個の加群生成元の像の差を消し、元の環への射を商へ降ろす。
規約：係数環の Noether 性は要求しない。実際の全射な商写像と可換式を返す。
使われ方：整拡大の有限表示模型の添字圏の filtered 性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R C D B : Type u} [CommRing R] [CommRing C] [CommRing D] [CommRing B]
variable [Algebra R C] [Algebra R D] [Algebra R B]

/-- 元の環への射で一致する平行射は、有限・有限表示の商模型で等しくできる。 -/
theorem exists_finite_finitePresentation_coequalizing_quotient
    [Module.Finite R C] [Module.Finite R D] [Algebra.FinitePresentation R D]
    (f g : C →ₐ[R] D) (h : D →ₐ[R] B) (hh : h.comp f = h.comp g) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra R Q),
      Module.Finite R Q ∧ Algebra.FinitePresentation R Q ∧
      ∃ (q : D →ₐ[R] Q) (_ : Function.Surjective q) (h' : Q →ₐ[R] B),
        h'.comp q = h ∧ q.comp f = q.comp g := by
  classical
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := R) (M := C)
  let d : Fin n → D := fun i ↦ f (b i) - g (b i)
  let J := Ideal.span (Set.range d)
  have hJ : J.FG := ⟨Finset.univ.image d, by simp [J]⟩
  have hJker : J ≤ RingHom.ker h.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    change h (f (b i) - g (b i)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (DFunLike.congr_fun hh (b i))
  let Q := D ⧸ J
  have : Algebra.FinitePresentation R Q := Algebra.FinitePresentation.quotient hJ
  let q : D →ₐ[R] Q := Ideal.Quotient.mkₐ R J
  let h' : Q →ₐ[R] B := Ideal.Quotient.liftₐ J h
    (fun a ha ↦ RingHom.mem_ker.mp (hJker ha))
  have heq : q.comp f = q.comp g := by
    apply AlgHom.toLinearMap_injective
    apply LinearMap.ext_on_range hb
    intro i
    change Ideal.Quotient.mk J (f (b i)) = Ideal.Quotient.mk J (g (b i))
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_range_self i))
  refine ⟨Q, inferInstance, inferInstance, inferInstance, inferInstance,
    q, Ideal.Quotient.mkₐ_surjective R J, h', ?_, heq⟩
  exact Ideal.Quotient.liftₐ_comp J h _

end SerrePositivity.AlgebraicGeometry
