module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFiniteNormalizedTowerFlat
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFirstCoefficientPowerEquiv

/-! # 初期有限正規化商と適切な係数商上の根添加環の比較 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 零段有限変数の唯一の段添字を除く標準多項式代数同型。 -/
def deltaDivisionFiniteNormalizedInitialVariableEquiv :
    MvPolynomial (σ × Fin 1) A ≃ₐ[A] MvPolynomial σ A :=
  MvPolynomial.renameEquiv A (Equiv.prodUnique σ (Fin 1))

/-- 零段有限イデアルは既存の第一係数多項式イデアルに移る。 -/
theorem deltaDivisionFiniteNormalizedPresentationIdeal_map_finOne (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    Ideal.map (deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)).toRingHom
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a u 0) =
      deltaDivisionFirstPolynomialIdeal D d a u := by
  have hz : Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u 0)) = ⊥ := by
    apply le_bot_iff.mp
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact Fin.elim0 i
  unfold deltaDivisionFiniteNormalizedPresentationIdeal
  rw [hz, sup_bot_eq]
  simp only [deltaDivisionFirstPolynomialIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_pair, ← Set.range_comp']
  simp [deltaDivisionFiniteNormalizedInitialVariableEquiv]

/-- 初期有限正規化商はA/(p,d,a_s)上の既存通常根添加環に同型。 -/
def deltaDivisionFiniteNormalizedInitialPowerEquiv (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    DeltaDivisionFiniteNormalizedQuotient D d a u 0 ≃+* DeltaDivisionFirstPowerCover D d a u :=
  (Ideal.quotientEquiv _ _
    (deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)).toRingEquiv
    (deltaDivisionFiniteNormalizedPresentationIdeal_map_finOne D d a u).symm).trans
    (deltaDivisionFirstCoefficientPowerEquiv D d a u)

/-- 初期商比較は基底係数の標準像を適切な係数商の係数射へ送る。 -/
theorem deltaDivisionFiniteNormalizedInitialPowerEquiv_C (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
      algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ b) := by
  change deltaDivisionFirstCoefficientPowerEquiv D d a u
    (Ideal.Quotient.mk _ (deltaDivisionFiniteNormalizedInitialVariableEquiv (MvPolynomial.C b))) = _
  have hc : deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)
      (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [deltaDivisionFiniteNormalizedInitialVariableEquiv]
  rw [hc, deltaDivisionFirstCoefficientPowerEquiv_coeff]

/-- 初期商比較は初期変数の標準商像を指定したp乗根へ送る。 -/
theorem deltaDivisionFiniteNormalizedInitialPowerEquiv_X (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u
      (Ideal.Quotient.mk _ (MvPolynomial.X (s, (0 : Fin 1)))) =
      monicPowerFamilyRoot p σ _ (deltaDivisionFirstPowerCoefficients D d a u) s := by
  change deltaDivisionFirstCoefficientPowerEquiv D d a u
    (Ideal.Quotient.mk _ (deltaDivisionFiniteNormalizedInitialVariableEquiv
      (MvPolynomial.X (s, (0 : Fin 1))))) = _
  have hx : deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)
      (MvPolynomial.X (s, (0 : Fin 1))) = MvPolynomial.X s := by
    simp [deltaDivisionFiniteNormalizedInitialVariableEquiv]
  rw [hx, deltaDivisionFirstCoefficientPowerEquiv_root]

end SerrePositivity.BhattScholze
