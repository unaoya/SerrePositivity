module

public import SerrePositivity.BhattScholze.DeltaDivisionEvaluationSource

/-! # 分母1の実raw δ包と源評価環

自由δ射x↦1·zは恒等射なので、そのraw包は実源評価環そのものとなる。
標準商射・基底射・変数・δ構造との両立を保つ。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 実源δ評価射は、元の係数射を切断として全射。 -/
theorem deltaDivisionSourceEval_surjective (D : DeltaStructure p A) (a : σ → A) :
    Function.Surjective (deltaDivisionSourceEval D a) := by
  intro r
  exact ⟨MvPolynomial.C r, deltaDivisionSourceEval_C D a r⟩

/-- 分母1を指定する自由δ射は実恒等射。 -/
theorem deltaDivisionSourceMap_one (D : DeltaStructure p A) :
    deltaDivisionSourceMap (σ := σ) D (1 : A) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    exact deltaDivisionSourceMap_C D 1 r
  · rintro ⟨s, n⟩
    rw [deltaDivisionSourceMap_X, map_one, one_mul]
    have h := relativeFreeDeltaHom_X_iterates D (relativeFreeDeltaStructure σ D)
      (RingHom.id (RelativeFreeDeltaRing (R := A) σ)) (fun _ => rfl) s n
    exact h.symm

/-- 分母1の実定義δ閉包は、実源評価射の核。 -/
theorem deltaDivisionUnitDenominator_ideal (D : DeltaStructure p A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal (1 : A) a) =
      RingHom.ker (deltaDivisionSourceEval D a) := by
  have h := deltaDivisionSourceMap_eval_ker D (1 : A) a
  rw [deltaDivisionSourceMap_one, Ideal.map_id] at h
  exact h.symm

/-- 分母1のraw δ包と評価環Aの具体的な環同型。 -/
def deltaDivisionUnitDenominatorEquiv (D : DeltaStructure p A) (a : σ → A) :
    DeltaAdjoinDivision D (1 : A) a ≃+* A :=
  (Ideal.quotEquivOfEq (deltaDivisionUnitDenominator_ideal D a)).trans
    ((deltaDivisionSourceEval D a).quotientKerEquivOfSurjective
      (deltaDivisionSourceEval_surjective D a))

/-- 分母1のraw比較は、標準商元を実源δ評価値へ送る。 -/
theorem deltaDivisionUnitDenominatorEquiv_mk (D : DeltaStructure p A) (a : σ → A)
    (r : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ r) =
      deltaDivisionSourceEval D a r := by
  rw [deltaDivisionUnitDenominatorEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- 実raw包への基底標準射は、分母1の比較同型で恒等射になる。 -/
theorem deltaDivisionUnitDenominatorEquiv_comp_base (D : DeltaStructure p A) (a : σ → A) :
    (deltaDivisionUnitDenominatorEquiv D a).toRingHom.comp (deltaAdjoinDivisionMap D (1 : A) a) =
      RingHom.id A := by
  apply RingHom.ext
  intro r
  change deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ (MvPolynomial.C r)) = r
  rw [deltaDivisionUnitDenominatorEquiv_mk, deltaDivisionSourceEval_C]

/-- 添加変数は、実評価環の指定元となる。 -/
theorem deltaDivisionUnitDenominatorEquiv_variable (D : DeltaStructure p A) (a : σ → A) (s : σ) :
    deltaDivisionUnitDenominatorEquiv D a (deltaAdjoinDivisionVariable D (1 : A) a s) = a s := by
  change deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ (MvPolynomial.X (s, 0))) = _
  rw [deltaDivisionUnitDenominatorEquiv_mk, deltaDivisionSourceEval_X]
  rfl

/-- 分母1の比較同型の逆射は、既存の実基底標準射そのもの。 -/
theorem deltaDivisionUnitDenominatorEquiv_symm_apply (D : DeltaStructure p A) (a : σ → A) (r : A) :
    (deltaDivisionUnitDenominatorEquiv D a).symm r = deltaAdjoinDivisionMap D (1 : A) a r := by
  apply (deltaDivisionUnitDenominatorEquiv D a).injective
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (deltaDivisionUnitDenominatorEquiv_comp_base D a) r).symm

/-- 分母1の実環同型は、既存raw δ構造を保つ。 -/
theorem deltaDivisionUnitDenominatorEquiv_isDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    (deltaAdjoinDivisionStructure D (1 : A) a).IsDeltaHom D
      (deltaDivisionUnitDenominatorEquiv D a).toRingHom := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change deltaDivisionUnitDenominatorEquiv D a
      ((deltaAdjoinDivisionStructure D (1 : A) a).delta (Ideal.Quotient.mk _ r)) =
    D.delta (deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ r))
  rw [deltaAdjoinDivisionStructure, DeltaStructure.quotient_delta_mk,
    deltaDivisionUnitDenominatorEquiv_mk, deltaDivisionUnitDenominatorEquiv_mk]
  exact deltaDivisionSourceEval_isDeltaHom D a r

end SerrePositivity.BhattScholze
