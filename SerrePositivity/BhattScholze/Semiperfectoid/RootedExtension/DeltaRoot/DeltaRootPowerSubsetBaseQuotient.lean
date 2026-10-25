module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootPowerSubsetRegular

/-! # 先行根関係のp乗商と係数商の標準比較 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (I : Ideal A) (T : Set σ) (b : σ → A)
local notation "J" => Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p)
local notation "Jbar" => Ideal.span (Set.range fun t : T ↦
  (deltaRootRelationFamily (p := p) (fun s ↦ Ideal.Quotient.mk I (b s)) t) ^ p)
local notation "IB" => I.map (MvPolynomial.C : A →+* MvPolynomial σ A)

omit [Fact p.Prime] in
/-- 先行根関係のp乗イデアルは係数商の下で対応するイデアルに写る。 -/
theorem deltaRootPowerSubsetIdeal_map_coefficientQuotient :
    ((J).map (Ideal.Quotient.mk IB)).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom = Jbar := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [Ideal.map_span, ← Set.range_comp', deltaRootRelationFamily,
    map_pow, map_sub, MvPolynomial.map_X, MvPolynomial.map_C]

/-- 係数イデアルと先行根関係のp乗による商の具体的な標準同型。 -/
def deltaRootPowerSubsetBaseQuotientEquiv :
    (MvPolynomial σ A ⧸ (IB ⊔ J)) ≃+* (MvPolynomial σ (A ⧸ I) ⧸ Jbar) :=
  (DoubleQuot.quotQuotEquivQuotSup IB J).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (deltaRootPowerSubsetIdeal_map_coefficientQuotient (p := p) I T b).symm)

omit [Fact p.Prime] in
/-- 標準同型は多項式の係数を商へ送る写像で与えられる。 -/
theorem deltaRootPowerSubsetBaseQuotientEquiv_mk (x : MvPolynomial σ A) :
    deltaRootPowerSubsetBaseQuotientEquiv (p := p) I T b (Ideal.Quotient.mk (IB ⊔ J) x) =
      Ideal.Quotient.mk Jbar (MvPolynomial.map (Ideal.Quotient.mk I) x) := by
  change Ideal.Quotient.mk Jbar
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
      (Ideal.Quotient.mk IB x)) = _
  congr 1
  exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ A I) x

/-- pと先行根関係のp乗で割っても、残りの根関係は正則。 -/
theorem deltaRootPowerSubsetModP_remaining_isSMulRegular
    (T : Set σ) (b : σ → A) (s : σ) (hs : s ∉ T) :
    IsSMulRegular
      (MvPolynomial σ A ⧸ (Ideal.span {(p : MvPolynomial σ A)} ⊔
        Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p)))
      (Ideal.Quotient.mk
        (Ideal.span {(p : MvPolynomial σ A)} ⊔
          Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
        (deltaRootRelationFamily (p := p) b s)) := by
  let I := Ideal.span {(p : A)}
  let e := deltaRootPowerSubsetBaseQuotientEquiv (p := p) I T b
  have hp : (p : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hr := deltaRootSubsetPowerQuotient_remaining_isSMulRegular hp T
    (fun t ↦ Ideal.Quotient.mk I (b t)) s hs
  have he : e (Ideal.Quotient.mk _ (deltaRootRelationFamily (p := p) b s)) =
      Ideal.Quotient.mk _
        (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) := by
    rw [deltaRootPowerSubsetBaseQuotientEquiv_mk]
    simp only [deltaRootRelationFamily, map_sub, map_pow, MvPolynomial.map_X,
      MvPolynomial.map_C]
  have hreg : IsSMulRegular (MvPolynomial σ A ⧸
      (I.map MvPolynomial.C ⊔ Ideal.span
        (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p)))
      (Ideal.Quotient.mk
        (I.map MvPolynomial.C ⊔ Ideal.span
          (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
        (deltaRootRelationFamily (p := p) b s)) := by
    intro x y hxy
    apply e.injective
    apply hr
    have h := congrArg e hxy
    simpa only [smul_eq_mul, map_mul, he] using h
  have hI : I.map (MvPolynomial.C : A →+* MvPolynomial σ A) =
      Ideal.span {(p : MvPolynomial σ A)} := by
    simp only [I, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hI] at hreg
  exact hreg

end SerrePositivity.BhattScholze
