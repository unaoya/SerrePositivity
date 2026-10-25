module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionNormalizedStepSourceQuotient
public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteVariableSplit

/-! # 全相対自由環の下位正規化関係商と有限実源商の比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "J" => deltaDivisionFirstResidueIdeal D d a ⊔
  deltaDivisionFiniteNormalizedWittIdeal D d a v N
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 有限実源商の表示イデアルの初期包含像は、全自由環の下位正規化イデアル。 -/
theorem deltaDivisionNormalizedStepSourceIdeal_map_initial (hv : (v : A) = D.delta d) :
    (deltaDivisionNormalizedStepSourceIdeal D d a v N).map
      (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A).toRingHom = J := by
  unfold deltaDivisionNormalizedStepSourceIdeal
  rw [Ideal.map_map, relativeFreeFiniteStepInclusion_comp_initial]
  exact deltaDivisionFiniteNormalizedPresentationIdeal_map_initial D d a v hv N

/-- 全自由環の下位正規化イデアルは、後続変数分離で係数イデアルへ移る。 -/
theorem deltaDivisionNormalizedAmbientSourceIdeal_map_split (hv : (v : A) = D.delta d) :
    Ideal.map (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingHom J =
      (deltaDivisionNormalizedStepSourceIdeal D d a v N).map
        (MvPolynomial.C : MvPolynomial (σ × Fin (N + 2)) A →+*
          MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin (N + 2)) A)) := by
  rw [← deltaDivisionNormalizedStepSourceIdeal_map_initial D d a v N hv, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact relativeFreeFiniteVariableSplitAlgEquiv_initial (N + 2) σ A f

/-- 全自由環の下位正規化関係商は、有限実源商上の後続多項式環。 -/
def deltaDivisionNormalizedAmbientSourceEquiv (hv : (v : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ J) ≃+* MvPolynomial (σ × ℕ) S₀ :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingEquiv
    (deltaDivisionNormalizedAmbientSourceIdeal_map_split D d a v N hv).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ)
      (deltaDivisionNormalizedStepSourceIdeal D d a v N)).symm.toRingEquiv

/-- 比較同型は全自由環の標準商射上で、分離後の係数商写像と一致する。 -/
theorem deltaDivisionNormalizedAmbientSourceEquiv_mk (hv : (v : A) = D.delta d)
    (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N))
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)))
    MvPolynomial.X (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N))
      (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 初期有限多項式の商像は、有限実源商の標準係数像に一致する。 -/
theorem deltaDivisionNormalizedAmbientSourceEquiv_initial (hv : (v : A) = D.delta d)
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
      (Ideal.Quotient.mk _ (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A f)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N) f) := by
  rw [deltaDivisionNormalizedAmbientSourceEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, MvPolynomial.map_C]

/-- 全自由環の下位正規化関係商でも、次のモニック関係の初期包含像は非零因子。 -/
theorem deltaDivisionNormalizedAmbientSource_relation_isSMulRegular
    (hv : (v : A) = D.delta d) (s : σ) :
    IsSMulRegular (RelativeFreeDeltaRing (R := A) σ ⧸ J)
      (Ideal.Quotient.mk J (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a v s N))) := by
  have hr : IsSMulRegular S₀
      (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
    have h := deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular
      D d a v N (fun _ : Fin 1 ↦ s) (fun _ _ _ ↦ Subsingleton.elim _ _)
    simpa only [List.ofFn_const, List.replicate_one,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] using h
  let e := deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
  have he := deltaDivisionNormalizedAmbientSourceEquiv_initial D d a v N hv
    (deltaDivisionWittNormalizedPolynomial D d a v s N)
  change e (Ideal.Quotient.mk J (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
    (deltaDivisionWittNormalizedPolynomial D d a v s N))) = _ at he
  intro f g hfg
  apply e.injective
  apply MvPolynomial.ext
  intro k
  apply hr
  have h := congrArg (fun z ↦ (e z).coeff k) hfg
  simpa only [smul_eq_mul, map_mul, he, MvPolynomial.coeff_C_mul] using h

end SerrePositivity.BhattScholze
