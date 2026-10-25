module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteNormalizedStep
public import SerrePositivity.BhattScholze.Andre.RootedExtension.MonicPowerFamilyBaseQuotient

/-! # 有限正規化商の一段を前段商上のモニック冪根添加として実現 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 既存の有限正規化表示イデアルによる通常商環。 -/
abbrev DeltaDivisionFiniteNormalizedQuotient (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :=
  MvPolynomial (σ × Fin (N + 1)) A ⧸
    deltaDivisionFiniteNormalizedPresentationIdeal D d a u N

/-- 次段のモニック冪関係の係数は、具体的下位多項式の前段商像。 -/
def deltaDivisionFiniteNormalizedStepCoefficients (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : σ → DeltaDivisionFiniteNormalizedQuotient D d a u N :=
  fun s => Ideal.Quotient.mk _ (deltaDivisionWittNormalizedCoefficient D d a u s N)

/-- 次段有限正規化商は、前段商上の任意添字族モニック冪根添加環に同型。 -/
def deltaDivisionFiniteNormalizedStepPowerEquiv (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :
    DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1) ≃+*
      MonicPowerFamilyCover p σ (DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (deltaDivisionFiniteNormalizedStepCoefficients D d a u N) :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingEquiv
    (deltaDivisionFiniteNormalizedPresentationIdeal_map_top_split D d a u N).symm).trans
    (monicPowerFamilyBaseQuotientEquiv p σ (MvPolynomial (σ × Fin (N + 1)) A)
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N)
      (fun s => deltaDivisionWittNormalizedCoefficient D d a u s N))

/-- 次段商同型は前段の標準包含を根添加環の係数射に送る。 -/
theorem deltaDivisionFiniteNormalizedStepPowerEquiv_inclusion (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N
      (Ideal.Quotient.mk _ (relativeFreeFiniteStepInclusion N σ f)) =
      algebraMap (DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (MonicPowerFamilyCover p σ (DeltaDivisionFiniteNormalizedQuotient D d a u N)
          (deltaDivisionFiniteNormalizedStepCoefficients D d a u N))
        (Ideal.Quotient.mk _ f) := by
  change monicPowerFamilyBaseQuotientEquiv p σ (MvPolynomial (σ × Fin (N + 1)) A) _ _
    (Ideal.Quotient.mk _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
      (relativeFreeFiniteStepInclusion N σ f))) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion,
    monicPowerFamilyBaseQuotientEquiv_C]
  rfl

/-- 次段商同型は最高変数を指定したp乗根に送る。 -/
theorem deltaDivisionFiniteNormalizedStepPowerEquiv_top (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (s : σ) :
    deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N
      (Ideal.Quotient.mk _ (MvPolynomial.X (s, Fin.last (N + 1)))) =
      monicPowerFamilyRoot p σ (DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (deltaDivisionFiniteNormalizedStepCoefficients D d a u N) s := by
  change monicPowerFamilyBaseQuotientEquiv p σ (MvPolynomial (σ × Fin (N + 1)) A) _ _
    (Ideal.Quotient.mk _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
      (MvPolynomial.X (s, Fin.last (N + 1))))) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_X_top, monicPowerFamilyBaseQuotientEquiv_X]
  rfl

end SerrePositivity.BhattScholze
