module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSecondMonicPresentation
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteVariableSplit
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # 第2通常δ剰余を係数とする後続多項式表示

二つのモニック方程式を有限初期変数の係数イデアルへ移す。
この係数商と同時根添加環の比較は別工程。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 二つの初期変数のみの多項式環に置いた係数・モニック関係式のイデアル。 -/
def deltaDivisionSecondPolynomialIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (MvPolynomial (σ × Fin 2) A) :=
  ((Ideal.span {(p : MvPolynomial (σ × Fin 2) A), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, 1) ^ p -
      MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s))

/-- 第0変数の有限分離像。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_two_zero (s : σ) :
    relativeFreeFiniteVariableSplitAlgEquiv 2 σ A (MvPolynomial.X (s, 0)) =
      MvPolynomial.C (MvPolynomial.X (s, (0 : Fin 2))) :=
  relativeFreeFiniteVariableSplitAlgEquiv_X_initial 2 σ A s 0

/-- 第1変数の有限分離像。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_two_one (s : σ) :
    relativeFreeFiniteVariableSplitAlgEquiv 2 σ A (MvPolynomial.X (s, 1)) =
      MvPolynomial.C (MvPolynomial.X (s, (1 : Fin 2))) :=
  relativeFreeFiniteVariableSplitAlgEquiv_X_initial 2 σ A s 1

/-- 第2モニックイデアルは有限初期係数イデアルの延長へ送られる。 -/
theorem deltaDivisionSecondMonicIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (deltaDivisionSecondMonicIdeal D d a u).map
      (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A).toRingHom =
      (deltaDivisionSecondPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial (σ × Fin 2) A →+*
          MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin 2) A)) := by
  simp only [deltaDivisionSecondMonicIdeal, deltaDivisionFirstMonicIdeal,
    deltaDivisionSecondPolynomialIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_pair, ← Set.range_comp']
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    map_natCast, relativeFreeFiniteVariableSplitAlgEquiv_C,
    relativeFreeFiniteVariableSplitAlgEquiv_two_zero,
    relativeFreeFiniteVariableSplitAlgEquiv_two_one,
    map_sub, map_pow]

/-- 実際の第2通常剰余イデアルは係数イデアルの延長へ送られる。 -/
theorem deltaDivisionSecondResidueIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (deltaDivisionSecondResidueIdeal D d a).map
      (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A).toRingHom =
      (deltaDivisionSecondPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial (σ × Fin 2) A →+*
          MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin 2) A)) := by
  rw [deltaDivisionSecondResidueIdeal_eq_monic D d a u hu,
    deltaDivisionSecondMonicIdeal_map_split]

/-- 実際の第2通常δ剰余は、有限初期多項式商上の後続変数の多項式環。 -/
def deltaDivisionSecondResiduePolynomialEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) ≃+*
      MvPolynomial (σ × ℕ)
        (MvPolynomial (σ × Fin 2) A ⧸ deltaDivisionSecondPolynomialIdeal D d a u) :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A).toRingEquiv
    (deltaDivisionSecondResidueIdeal_map_split D d a u hu).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := σ × ℕ) (deltaDivisionSecondPolynomialIdeal D d a u)).symm.toRingEquiv

/-- 第2後続多項式表示は標準商射と係数の商写像に両立する。 -/
theorem deltaDivisionSecondResiduePolynomialEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) x) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u))
        (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A x) := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u)))
    MvPolynomial.X (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A x) = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 両初期変数は有限係数商の指定変数となる。 -/
@[simp] theorem deltaDivisionSecondResiduePolynomialEquiv_initial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (i : Fin 2) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.X (s, i.val))) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u)
        (MvPolynomial.X (s, i))) := by
  rw [deltaDivisionSecondResiduePolynomialEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_X_initial, MvPolynomial.map_C]

/-- 第2段以降の変数は外側の自由変数となる。 -/
@[simp] theorem deltaDivisionSecondResiduePolynomialEquiv_tail
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (n : ℕ) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.X (s, n + 2))) =
      MvPolynomial.X (s, n) := by
  rw [deltaDivisionSecondResiduePolynomialEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_X_tail, MvPolynomial.map_X]

/-- 元の係数は有限係数商の標準像となる。 -/
@[simp] theorem deltaDivisionSecondResiduePolynomialEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.C r)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u)
        (MvPolynomial.C r)) := by
  rw [deltaDivisionSecondResiduePolynomialEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_C, MvPolynomial.map_C]

end SerrePositivity.BhattScholze
