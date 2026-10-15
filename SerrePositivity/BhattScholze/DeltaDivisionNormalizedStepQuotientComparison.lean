module

public import SerrePositivity.BhattScholze.DeltaDivisionNormalizedStepSourceQuotient

/-! # 最高段関係を課した二重商と次段実正規化商の比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 前段関係の実源商内の最高段関係イデアル。 -/
def deltaDivisionNormalizedStepTopIdeal :
    Ideal (MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N) :=
  (Ideal.span (Set.range fun s ↦ deltaDivisionWittNormalizedPolynomial D d a v s N)).map
    (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N))

/-- 最高段イデアルは実源商内の関係式像のspan。 -/
theorem deltaDivisionNormalizedStepTopIdeal_eq_span :
    deltaDivisionNormalizedStepTopIdeal D d a v N =
      Ideal.span (Set.range fun s ↦
        Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
          (deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
  rw [deltaDivisionNormalizedStepTopIdeal, Ideal.map_span, ← Set.range_comp']

/-- 前段包含像と最高段関係を合わせたイデアルは、既存の次段表示イデアル。 -/
theorem deltaDivisionNormalizedStepSourceIdeal_sup_top :
    deltaDivisionNormalizedStepSourceIdeal D d a v N ⊔
      Ideal.span (Set.range fun s ↦ deltaDivisionWittNormalizedPolynomial D d a v s N) =
      deltaDivisionFiniteNormalizedPresentationIdeal D d a v (N + 1) :=
  (deltaDivisionFiniteNormalizedPresentationIdeal_succ D d a v N).symm

/-- 実源商に最高段関係を課した二重商は、既存の次段実正規化商。 -/
def deltaDivisionNormalizedStepDoubleQuotientEquiv :
    ((MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N) ⧸
      deltaDivisionNormalizedStepTopIdeal D d a v N) ≃+*
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) :=
  (DoubleQuot.quotQuotEquivQuotSup (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (Ideal.span (Set.range fun s ↦ deltaDivisionWittNormalizedPolynomial D d a v s N))).trans
    (Ideal.quotEquivOfEq (deltaDivisionNormalizedStepSourceIdeal_sup_top D d a v N))

/-- 比較同型は元の多項式の二重商像を次段の標準商像へ送る。 -/
theorem deltaDivisionNormalizedStepDoubleQuotientEquiv_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) = Ideal.Quotient.mk _ f := by
  change Ideal.quotEquivOfEq (deltaDivisionNormalizedStepSourceIdeal_sup_top D d a v N)
    (DoubleQuot.quotQuotEquivQuotSup _ _
    (DoubleQuot.quotQuotMk _ _ f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
  rfl

/-- 有限添字の場合、最高段全関係の列は実源商上のKoszul分解を与える。 -/
theorem deltaDivisionNormalizedStepAll_isKoszulResolution [Fintype σ] :
    SerrePositivity.IsKoszulResolution (fun i : Fin (Fintype.card σ) ↦
      Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v ((Fintype.equivFin σ).symm i) N)) :=
  deltaDivisionNormalizedStepSourceRelation_fin_isKoszulResolution D d a v N
    (Fintype.equivFin σ).symm (Fintype.equivFin σ).symm.injective

/-- 有限列挙による全最高段関係のspanは、実際の最高段イデアル。 -/
theorem deltaDivisionNormalizedStepAll_span [Fintype σ] :
    Ideal.span (Set.range fun i : Fin (Fintype.card σ) ↦
      Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v ((Fintype.equivFin σ).symm i) N)) =
      deltaDivisionNormalizedStepTopIdeal D d a v N := by
  rw [deltaDivisionNormalizedStepTopIdeal_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin σ).symm i, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨Fintype.equivFin σ s, ?_⟩
    simp only [Equiv.symm_apply_apply]

end SerrePositivity.BhattScholze
