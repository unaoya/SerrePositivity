module

public import SerrePositivity.CommutativeAlgebra.Perfectoidization
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor

/-! # 旧有限代数選択との互換比較

このモジュールだけは旧B-Iに相対的である。B3で選ぶ主イデアル商と旧選択を
標準写像と両立する同型で比較する。巡回評価の実経路からはimportしない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- B3で選ぶ商と旧有限代数の選択は、商環からの標準写像を保って同型になる。 -/
theorem exists_quotientPerfectoidization_equiv_finiteChoice :
    letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
    ∃ e : QuotientPerfectoidization R (Ideal.span {g}) p hR ≃+*
        Perfectoidization R (R ⧸ Ideal.span {g}) p hR,
      e.toRingHom.comp (toQuotientPerfectoidization R (Ideal.span {g}) p hR) =
        toPerfectoidization R (R ⧸ Ideal.span {g}) p hR := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  exact (isPerfectoidization_toQuotientPerfectoidization R _ p hR).exists_equiv p
    (isPerfectoidization_toPerfectoidization R (R ⧸ Ideal.span {g}) p hR)

/-- 新しいperfectoid idealは、旧選択を使った核と一致する。 -/
theorem perfectoidIdeal_eq_finiteChoice_kernel :
    letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
    perfectoidIdeal R p hR g = RingHom.ker
      ((toPerfectoidization R (R ⧸ Ideal.span {g}) p hR).comp
        (Ideal.Quotient.mk (Ideal.span {g}))) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  exact (isPerfectoidization_toQuotientPerfectoidization R _ p hR).ker_comp_eq p
    (isPerfectoidization_toPerfectoidization R (R ⧸ Ideal.span {g}) p hR)
    (Ideal.Quotient.mk (Ideal.span {g}))

end SerrePositivity
