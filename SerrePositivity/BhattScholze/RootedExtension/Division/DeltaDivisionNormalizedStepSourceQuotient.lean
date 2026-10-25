module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionNormalizedStepKoszul

/-! # 前段関係だけで割った実源商と最高段関係の正則性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 次段源多項式環内の、前段表示イデアルの標準包含像。 -/
def deltaDivisionNormalizedStepSourceIdeal : Ideal (MvPolynomial (σ × Fin (N + 2)) A) :=
  (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N).map
    (relativeFreeFiniteStepInclusion N σ)

/-- 最高変数分離は前段関係の包含像を係数イデアルへ送る。 -/
theorem deltaDivisionNormalizedStepSourceIdeal_map_split :
    (deltaDivisionNormalizedStepSourceIdeal D d a v N).map
      (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom =
    (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N).map
      (MvPolynomial.C : MvPolynomial (σ × Fin (N + 1)) A →+*
        MvPolynomial σ (MvPolynomial (σ × Fin (N + 1)) A)) := by
  unfold deltaDivisionNormalizedStepSourceIdeal
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion N σ A f

/-- 前段関係だけで割った実源商は、前段実商上の最高変数の多項式環。 -/
def deltaDivisionNormalizedStepSourceQuotientEquiv :
    (MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N) ≃+*
      MvPolynomial σ (DeltaDivisionFiniteNormalizedQuotient D d a v N) :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingEquiv
    (deltaDivisionNormalizedStepSourceIdeal_map_split D d a v N).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ)
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N)).symm.toRingEquiv

/-- 実源商の同型は、前工程の具体的標準射と一致する。 -/
theorem deltaDivisionNormalizedStepSourceQuotientEquiv_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N (Ideal.Quotient.mk _ f) =
      deltaDivisionNormalizedStepPolynomialMap D d a v N f := by
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk _)) MvPolynomial.X
    (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk _) (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 前段関係だけで割った実源商内でも、有限個の最高段関係は弱正則列。 -/
theorem deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N)
      (List.ofFn fun i ↦ Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  let e := deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N
  let rs := List.ofFn fun i ↦ Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, e,
      deltaDivisionNormalizedStepSourceQuotientEquiv_mk] using
      deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular D d a v N s hs

/-- 実源商内の最高段関係のKoszul複体は、対応する実通常商の分解。 -/
theorem deltaDivisionNormalizedStepSourceRelation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦
      Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular D d a v N s hs)

end SerrePositivity.BhattScholze
