module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionFirstResiduePresentation
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeVariableSplit
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # 初期δ剰余を係数とする後続変数の多項式表示

初期モニック関係式を係数イデアルへ移し、既存多項式商同型を使う。
この係数商の根添加環表示と、全δ段の平坦性は別途比較する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期変数のみの多項式環に置いた係数・モニック関係式のイデアル。 -/
def deltaDivisionFirstPolynomialIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (MvPolynomial σ A) :=
  (Ideal.span {(p : MvPolynomial σ A), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X s ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))

/-- 変数分離は初期モニックイデアルを係数イデアルの延長へ送る。 -/
theorem deltaDivisionFirstMonicIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (deltaDivisionFirstMonicIdeal D d a u).map
      (relativeFreeVariableSplitAlgEquiv σ A).toRingHom =
      (deltaDivisionFirstPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial σ A →+* MvPolynomial (σ × ℕ) (MvPolynomial σ A)) := by
  simp only [deltaDivisionFirstMonicIdeal, deltaDivisionFirstPolynomialIdeal,
    Ideal.map_sup, Ideal.map_span, Set.image_pair, ← Set.range_comp']
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, map_natCast, relativeFreeVariableSplitAlgEquiv_C,
    relativeFreeVariableSplitAlgEquiv_X_zero, map_sub, map_pow]

/-- 実際の低次δ剰余イデアルも、係数イデアルの延長へ送られる。 -/
theorem deltaDivisionFirstResidueIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (deltaDivisionFirstResidueIdeal D d a).map
      (relativeFreeVariableSplitAlgEquiv σ A).toRingHom =
      (deltaDivisionFirstPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial σ A →+* MvPolynomial (σ × ℕ) (MvPolynomial σ A)) := by
  rw [deltaDivisionFirstResidueIdeal_eq_monic D d a u hu,
    deltaDivisionFirstMonicIdeal_map_split]

/-- 実際の初期δ剰余は、初期関係式の商上の後続変数の多項式環。 -/
def deltaDivisionFirstResiduePolynomialEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial σ A ⧸ deltaDivisionFirstPolynomialIdeal D d a u) :=
  (Ideal.quotientEquiv _ _ (relativeFreeVariableSplitAlgEquiv σ A).toRingEquiv
    (deltaDivisionFirstResidueIdeal_map_split D d a u hu).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := σ × ℕ) (deltaDivisionFirstPolynomialIdeal D d a u)).symm.toRingEquiv

/-- 後続多項式表示は標準商射と係数の標準商写像に両立する。 -/
theorem deltaDivisionFirstResiduePolynomialEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) x) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u))
        (relativeFreeVariableSplitAlgEquiv σ A x) := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u)))
    MvPolynomial.X (relativeFreeVariableSplitAlgEquiv σ A x) = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 初期変数の剰余は係数商の指定変数となる。 -/
@[simp] theorem deltaDivisionFirstResiduePolynomialEquiv_initial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, 0))) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u)
        (MvPolynomial.X s)) := by
  rw [deltaDivisionFirstResiduePolynomialEquiv_mk,
    relativeFreeVariableSplitAlgEquiv_X_zero, MvPolynomial.map_C]

/-- 後続δ変数の剰余は外側の自由変数となる。 -/
@[simp] theorem deltaDivisionFirstResiduePolynomialEquiv_successor
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (n : ℕ) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, n + 1))) =
      MvPolynomial.X (s, n) := by
  rw [deltaDivisionFirstResiduePolynomialEquiv_mk,
    relativeFreeVariableSplitAlgEquiv_X_succ, MvPolynomial.map_X]

/-- 元の係数の剰余は係数商の標準像となる。 -/
@[simp] theorem deltaDivisionFirstResiduePolynomialEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.C r)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u)
        (MvPolynomial.C r)) := by
  rw [deltaDivisionFirstResiduePolynomialEquiv_mk,
    relativeFreeVariableSplitAlgEquiv_C, MvPolynomial.map_C]

end SerrePositivity.BhattScholze
