module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaAdjoinDivisionResidueFlat
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta

/-! # 根添加の多項式関係による具体的係数商 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 既存rank-one多項式δ環に置く、指定元族のp乗根の関係式。 -/
def deltaRootRelationFamily (b : σ → A) (s : σ) : MvPolynomial σ A :=
  MvPolynomial.X s ^ p - MvPolynomial.C (b s)

/-- 根関係族について既存除算包の係数商A[X_s]/(p,Cd,X_s^p-Cb_s)を使う。 -/
abbrev DeltaRootRelationCoefficientQuotient (d : A) (b : σ → A) :=
  MvPolynomial σ A ⧸
    deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)

omit [Fact p.Prime] in
/-- この係数イデアルは、(p,d)の係数拡張と既存モニック根関係イデアルの和。 -/
theorem deltaRootRelationCoefficientIdeal_eq_base_sup (d : A) (b : σ → A) :
    deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) =
      Ideal.map MvPolynomial.C (Ideal.span {(p : A), d}) ⊔
        monicPowerFamilyRelationIdeal p σ A b := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast, deltaDivisionFirstBaseIdeal,
    monicPowerFamilyRelationIdeal]
  rfl

/-- 指定根関係の係数商はA/(p,d)上の既存通常モニック根添加環に同型。 -/
def deltaRootRelationCoefficientPowerEquiv (d : A) (b : σ → A) :
    DeltaRootRelationCoefficientQuotient (p := p) d b ≃+*
      MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
        (fun s => Ideal.Quotient.mk _ (b s)) :=
  (Ideal.quotEquivOfEq (deltaRootRelationCoefficientIdeal_eq_base_sup d b)).trans
    (monicPowerFamilyBaseQuotientEquiv p σ A (Ideal.span {(p : A), d}) b)

omit [Fact p.Prime] in
/-- 根関係の係数商比較は基底係数の標準像に両立する。 -/
theorem deltaRootRelationCoefficientPowerEquiv_C (d : A) (b : σ → A) (c : A) :
    deltaRootRelationCoefficientPowerEquiv (p := p) d b
      (Ideal.Quotient.mk _ (MvPolynomial.C c)) =
      algebraMap (A ⧸ Ideal.span {(p : A), d})
        (MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
          (fun s => Ideal.Quotient.mk _ (b s))) (Ideal.Quotient.mk _ c) := by
  rw [deltaRootRelationCoefficientPowerEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, monicPowerFamilyBaseQuotientEquiv_C]

omit [Fact p.Prime] in
/-- 根関係の係数商比較は各多項式変数を指定p乗根に送る。 -/
theorem deltaRootRelationCoefficientPowerEquiv_X (d : A) (b : σ → A) (s : σ) :
    deltaRootRelationCoefficientPowerEquiv (p := p) d b
      (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      monicPowerFamilyRoot p σ (A ⧸ Ideal.span {(p : A), d})
        (fun t => Ideal.Quotient.mk _ (b t)) s := by
  rw [deltaRootRelationCoefficientPowerEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, monicPowerFamilyBaseQuotientEquiv_X]

end SerrePositivity.BhattScholze
