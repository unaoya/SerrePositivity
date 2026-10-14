module

public import SerrePositivity.CommutativeAlgebra.Perfectoidization
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor

/-! # perfectoid 化の普遍性による射とイデアルの比較

普遍写像を固定した perfectoid 化に、環準同型から誘導される射を構成する。
恒等射・合成との両立は一意性から証明する。perfectoid 化の存在は既存の引用に依存するが、
射の一意性を新たに引用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity


variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- 元の主イデアルは、その perfectoid イデアルに含まれる。 -/
theorem span_le_perfectoidIdeal (g : R) : Ideal.span {g} ≤ perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  apply Ideal.span_le.mpr
  intro x hx
  have hxg : x = g := Set.mem_singleton_iff.mp hx
  subst x
  change toPerfectoidization R (R ⧸ Ideal.span {g}) p hR
    (Ideal.Quotient.mk (Ideal.span {g}) g) = 0
  have hz : Ideal.Quotient.mk (Ideal.span {g}) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton g))
  rw [hz, map_zero]

/-- 単元のperfectoidイデアルは全体。全射性や商の被約性は必要ない。 -/
theorem perfectoidIdeal_eq_top_of_isUnit (g : R) (hg : IsUnit g) :
    perfectoidIdeal R p hR g = ⊤ := by
  apply top_unique
  have hh := span_le_perfectoidIdeal R p hR g
  rwa [Ideal.span_singleton_eq_top.mpr hg] at hh

/-- 主イデアルの包含は perfectoid イデアルの包含を与える。
商環間の写像を普遍性で perfectoid 化へ移し、核の包含を証明する。 -/
theorem perfectoidIdeal_mono {g k : R} (h : Ideal.span {g} ≤ Ideal.span {k}) :
    perfectoidIdeal R p hR g ≤ perfectoidIdeal R p hR k := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {k}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton k)
  let q : R ⧸ Ideal.span {g} →+* R ⧸ Ideal.span {k} := Ideal.Quotient.factor h
  let hg := isPerfectoidization_toPerfectoidization R (R ⧸ Ideal.span {g}) p hR
  let hk := isPerfectoidization_toPerfectoidization R (R ⧸ Ideal.span {k}) p hR
  intro x hx
  change toPerfectoidization R (R ⧸ Ideal.span {g}) p hR
    (Ideal.Quotient.mk (Ideal.span {g}) x) = 0 at hx
  change toPerfectoidization R (R ⧸ Ideal.span {k}) p hR
    (Ideal.Quotient.mk (Ideal.span {k}) x) = 0
  have he := RingHom.congr_fun (IsPerfectoidization.map_comp hg hk q)
    (Ideal.Quotient.mk (Ideal.span {g}) x)
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact he.symm

end SerrePositivity
