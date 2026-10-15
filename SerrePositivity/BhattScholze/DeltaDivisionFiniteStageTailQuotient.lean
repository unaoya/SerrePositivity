module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteLeadingLinear
public import SerrePositivity.BhattScholze.DeltaDivisionSecondFinitePresentation
public import SerrePositivity.BhattScholze.MonicPowerFamilyBaseQuotient

/-! # 初期有限δ関係商の後続多項式表示

実自由δ環上の通常商を、その関係が属する初期有限環の商と後続変数に分離する。
これは通常商の同型であり、導来δ基底変更の比較とは区別する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の初期有限イデアルを拡張した自由環商は、初期商上の後続多項式環。 -/
def relativeFreeFiniteInitialQuotientEquiv (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      J.map (relativeFreeFiniteInitialPolynomialMap n σ A).toRingHom) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin n) A ⧸ J) := by
  let e := relativeFreeFiniteVariableSplitAlgEquiv n σ A
  have h : (J.map (relativeFreeFiniteInitialPolynomialMap n σ A).toRingHom).map
      e.toRingHom = J.map MvPolynomial.C := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro f
    exact relativeFreeFiniteVariableSplitAlgEquiv_initial n σ A f
  exact (Ideal.quotientEquiv _ _ e.toRingEquiv h.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ) J).symm.toRingEquiv

/-- この同型の標準商射上の式。 -/
theorem relativeFreeFiniteInitialQuotientEquiv_mk (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) (f : RelativeFreeDeltaRing (R := A) σ) :
    relativeFreeFiniteInitialQuotientEquiv n J (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk J) (relativeFreeFiniteVariableSplitAlgEquiv n σ A f) := by
  rw [relativeFreeFiniteInitialQuotientEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp
    (σ × ℕ) (MvPolynomial (σ × Fin n) A) J)
    (relativeFreeFiniteVariableSplitAlgEquiv n σ A f)

/-- 初期側の元の像は、初期商の係数となる。 -/
theorem relativeFreeFiniteInitialQuotientEquiv_initial (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) (f : MvPolynomial (σ × Fin n) A) :
    relativeFreeFiniteInitialQuotientEquiv n J
      (Ideal.Quotient.mk _ (relativeFreeFiniteInitialPolynomialMap n σ A f)) =
      MvPolynomial.C (Ideal.Quotient.mk J f) := by
  rw [relativeFreeFiniteInitialQuotientEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, MvPolynomial.map_C]

/-- 後続変数の像はそのまま外側変数となる。 -/
theorem relativeFreeFiniteInitialQuotientEquiv_tail (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) (s : σ) (k : ℕ) :
    relativeFreeFiniteInitialQuotientEquiv n J
      (Ideal.Quotient.mk _ (MvPolynomial.X (s, k + n))) = MvPolynomial.X (s, k) := by
  rw [relativeFreeFiniteInitialQuotientEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_X_tail, MvPolynomial.map_X]

/-- 深さiの有限関係式を、固定した深さNの初期環へ含める。 -/
def deltaDivisionFiniteStageInitialRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) (s : σ) (i : Fin (N + 1)) : MvPolynomial (σ × Fin (N + 1)) A :=
  MvPolynomial.rename (fun z : σ × Fin (i.val + 1) =>
    (z.1, (⟨z.2.val, by omega⟩ : Fin (N + 1))))
      (deltaDivisionFiniteRelationPolynomial D d a s i.val)

/-- 固定初期環内に置いた関係の像は実際の反復δ関係。 -/
theorem deltaDivisionFiniteStageInitialRelation_image
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteInitialPolynomialMap (N + 1) σ A
      (deltaDivisionFiniteStageInitialRelation D d a N s i) =
        deltaDivisionIteratedRelation D d a s i.val := by
  rw [← deltaDivisionFiniteRelationPolynomial_image D d a s i.val]
  simp only [deltaDivisionFiniteStageInitialRelation, relativeFreeFiniteInitialPolynomialMap,
    MvPolynomial.rename_rename, Function.comp_def]

/-- 初期有限環内の全有限段関係イデアル。 -/
def deltaDivisionFiniteStageInitialIdeal (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) : Ideal (MvPolynomial (σ × Fin (N + 1)) A) :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    deltaDivisionFiniteStageInitialRelation D d a N z.1 z.2)

/-- 初期関係イデアルの拡張は既存の実自由環上の有限関係イデアルに一致する。 -/
theorem deltaDivisionFiniteStageInitialIdeal_map
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    (deltaDivisionFiniteStageInitialIdeal D d a N).map
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom =
        deltaDivisionFiniteRelationIdeal D d a N := by
  simp only [deltaDivisionFiniteStageInitialIdeal, Ideal.map_span, ← Set.range_comp',
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    deltaDivisionFiniteStageInitialRelation_image, deltaDivisionFiniteRelationIdeal]

/-- 実有限関係商を初期関係商上の後続多項式環へ分離する。 -/
def deltaDivisionFiniteStageTailQuotientEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFiniteRelationIdeal D d a N) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin (N + 1)) A ⧸
        deltaDivisionFiniteStageInitialIdeal D d a N) :=
  (Ideal.quotEquivOfEq (deltaDivisionFiniteStageInitialIdeal_map D d a N).symm).trans
    (relativeFreeFiniteInitialQuotientEquiv (N + 1) (deltaDivisionFiniteStageInitialIdeal D d a N))

/-- 実有限関係商の分離同型は標準商射と両立する。 -/
theorem deltaDivisionFiniteStageTailQuotientEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFiniteStageTailQuotientEquiv D d a N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionFiniteStageInitialIdeal D d a N))
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 1) σ A f) := by
  rw [deltaDivisionFiniteStageTailQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, relativeFreeFiniteInitialQuotientEquiv_mk]

/-- 次の実δ関係は、分離後も最高変数の一次式。残りは初期商の係数。 -/
theorem deltaDivisionFiniteStageTailQuotientEquiv_next
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) (s : σ) :
    deltaDivisionFiniteStageTailQuotientEquiv D d a N
      (Ideal.Quotient.mk _ (deltaDivisionIteratedRelation D d a s (N + 1))) =
        MvPolynomial.C (Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[N + 1] d))) *
          MvPolynomial.X (s, 0) +
        MvPolynomial.C (Ideal.Quotient.mk _
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1))) := by
  rw [deltaDivisionFiniteStageTailQuotientEquiv_mk,
    deltaDivisionIteratedRelation_eq_leading_add_lower]
  have hx := relativeFreeFiniteVariableSplitAlgEquiv_X_tail (N + 1) σ A s 0
  simp only [zero_add] at hx
  rw [map_add, map_mul, relativeFreeFiniteVariableSplitAlgEquiv_C, hx,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, map_add, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

/-- 全自由環上の有限関係商のp正則性は、初期有限関係商へ降りる。 -/
theorem deltaDivisionFiniteStageInitialQuotient_p_mul_injective
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
    (hp : Function.Injective (fun x : RelativeFreeDeltaRing (R := A) σ ⧸
      deltaDivisionFiniteRelationIdeal D d a N => (p : _) * x)) :
    Function.Injective (fun x : MvPolynomial (σ × Fin (N + 1)) A ⧸
      deltaDivisionFiniteStageInitialIdeal D d a N => (p : _) * x) := by
  let B := MvPolynomial (σ × Fin (N + 1)) A ⧸ deltaDivisionFiniteStageInitialIdeal D d a N
  let e := deltaDivisionFiniteStageTailQuotientEquiv D d a N
  have hp' : Function.Injective (fun x : MvPolynomial (σ × ℕ) B => (p : _) * x) := by
    intro x y h
    apply e.symm.injective
    apply hp
    have he := congrArg e.symm h
    simpa only [map_mul, map_natCast] using he
  intro x y h
  apply (MvPolynomial.C_injective (σ := σ × ℕ))
  apply hp'
  have hC : (MvPolynomial.C : B →+* MvPolynomial (σ × ℕ) B) (p : B) = p :=
    map_natCast _ p
  simpa only [map_mul, hC] using
    congrArg (MvPolynomial.C : B →+* MvPolynomial (σ × ℕ) B) h

end SerrePositivity.BhattScholze
