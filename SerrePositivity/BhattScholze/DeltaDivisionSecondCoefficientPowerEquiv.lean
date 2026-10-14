module

public import SerrePositivity.BhattScholze.DeltaDivisionSecondPowerPresentation
public import SerrePositivity.BhattScholze.DeltaDivisionFirstCoefficientPowerEquiv
public import SerrePositivity.BhattScholze.MonicPowerFamilyBaseQuotient

/-! # 第2有限係数商の同時根添加環表示

既存商比較同型を、具体的な二つの係数族とイデアルに適用する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 二つの初期p乗根の係数を一つの有限添字族へまとめる。 -/
def deltaDivisionTwoPowerCoefficients (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    σ × Fin 2 → A :=
  fun z => if z.2 = 0 then (u⁻¹ : Aˣ) * D.delta (a z.1)
    else deltaDivisionSecondPowerCoefficient D a d u z.1

/-- 適切な基底商上の二つの根族の通常同時根添加環。 -/
abbrev DeltaDivisionSecondPowerCover (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :=
  MonicPowerFamilyCover p (σ × Fin 2) (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
    (fun z => Ideal.Quotient.mk _ (deltaDivisionTwoPowerCoefficients D d a u z))

/-- 有限添字族のモニックイデアルは二つの指定モニックイデアルの和。 -/
theorem deltaDivisionTwoPowerRelationIdeal_eq
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    monicPowerFamilyRelationIdeal p (σ × Fin 2) A (deltaDivisionTwoPowerCoefficients D d a u) =
      Ideal.span (Set.range fun s => MvPolynomial.X (s, (0 : Fin 2)) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) ⊔
      Ideal.span (Set.range fun s => MvPolynomial.X (s, (1 : Fin 2)) ^ p -
        MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have h : i.val = 0 ∨ i.val = 1 := by omega
      rcases h with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hi with rfl | rfl
    · apply (show Ideal.span (Set.range fun t => MvPolynomial.X (t, (0 : Fin 2)) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a t))) ≤ _ from le_sup_left)
      exact Ideal.subset_span (Set.mem_range.mpr ⟨s, rfl⟩)
    · apply (show Ideal.span (Set.range fun t => MvPolynomial.X (t, (1 : Fin 2)) ^ p -
        MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u t)) ≤ _ from le_sup_right)
      exact Ideal.subset_span (Set.mem_range.mpr ⟨s, rfl⟩)
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, 0), rfl⟩)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, 1), rfl⟩)

/-- 実際の有限係数イデアルは基底イデアルと同時モニックイデアルの和。 -/
theorem deltaDivisionSecondPolynomialIdeal_eq_base_sup
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    deltaDivisionSecondPolynomialIdeal D d a u =
      (deltaDivisionFirstBaseIdeal (p := p) d a).map
        (MvPolynomial.C : A →+* MvPolynomial (σ × Fin 2) A) ⊔
      monicPowerFamilyRelationIdeal p (σ × Fin 2) A
        (deltaDivisionTwoPowerCoefficients D d a u) := by
  have hb : (deltaDivisionFirstBaseIdeal (p := p) d a).map
      (MvPolynomial.C : A →+* MvPolynomial (σ × Fin 2) A) =
      Ideal.span {(p : MvPolynomial (σ × Fin 2) A), MvPolynomial.C d} ⊔
        Ideal.span (Set.range fun s => MvPolynomial.C (a s)) := by
    simp only [deltaDivisionFirstBaseIdeal, Ideal.map_sup, Ideal.map_span,
      Set.image_pair, ← Set.range_comp', map_natCast]
  rw [hb, deltaDivisionTwoPowerRelationIdeal_eq, ← sup_assoc]
  rfl

/-- 第2有限係数商は適切な基底商上の同時根添加環。 -/
def deltaDivisionSecondCoefficientPowerEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (MvPolynomial (σ × Fin 2) A ⧸ deltaDivisionSecondPolynomialIdeal D d a u) ≃+*
      DeltaDivisionSecondPowerCover D d a u :=
  (Ideal.quotEquivOfEq (deltaDivisionSecondPolynomialIdeal_eq_base_sup D d a u)).trans
    (monicPowerFamilyBaseQuotientEquiv p (σ × Fin 2) A
      (deltaDivisionFirstBaseIdeal (p := p) d a) (deltaDivisionTwoPowerCoefficients D d a u))

set_option maxHeartbeats 1000000 in
-- 係数商・二重商・イデアル等式に沿う三つの商同型のカーネル比較に必要。
/-- 同時根添加比較は標準商射上で既存の係数商比較に一致する。 -/
theorem deltaDivisionSecondCoefficientPowerEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
    (x : MvPolynomial (σ × Fin 2) A) :
    deltaDivisionSecondCoefficientPowerEquiv D d a u (Ideal.Quotient.mk _ x) =
      monicPowerFamilyBaseQuotientEquiv p (σ × Fin 2) A
        (deltaDivisionFirstBaseIdeal (p := p) d a) (deltaDivisionTwoPowerCoefficients D d a u)
        (Ideal.Quotient.mk _ x) := by
  dsimp only [deltaDivisionSecondCoefficientPowerEquiv, RingEquiv.trans_apply]
  rw [Ideal.quotEquivOfEq_mk]

/-- 同時根添加比較は元の係数の標準像を保つ。 -/
@[simp] theorem deltaDivisionSecondCoefficientPowerEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    deltaDivisionSecondCoefficientPowerEquiv D d a u (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (DeltaDivisionSecondPowerCover D d a u) (Ideal.Quotient.mk _ r) := by
  rw [deltaDivisionSecondCoefficientPowerEquiv_mk]
  exact monicPowerFamilyBaseQuotientEquiv_C p (σ × Fin 2) A
    (deltaDivisionFirstBaseIdeal (p := p) d a) (deltaDivisionTwoPowerCoefficients D d a u) r

/-- 同時根添加比較は両変数を各指定根へ送る。 -/
@[simp] theorem deltaDivisionSecondCoefficientPowerEquiv_root
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (z : σ × Fin 2) :
    deltaDivisionSecondCoefficientPowerEquiv D d a u (Ideal.Quotient.mk _ (MvPolynomial.X z)) =
      monicPowerFamilyRoot p (σ × Fin 2) _
        (fun t => Ideal.Quotient.mk _ (deltaDivisionTwoPowerCoefficients D d a u t)) z := by
  rw [deltaDivisionSecondCoefficientPowerEquiv_mk]
  exact monicPowerFamilyBaseQuotientEquiv_X p (σ × Fin 2) A
    (deltaDivisionFirstBaseIdeal (p := p) d a) (deltaDivisionTwoPowerCoefficients D d a u) z

/-- 実際の第2通常δ剰余は同時根添加環上の後続多項式環。 -/
def deltaDivisionSecondResiduePowerPolynomialEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) ≃+*
      MvPolynomial (σ × ℕ) (DeltaDivisionSecondPowerCover D d a u) :=
  (deltaDivisionSecondResiduePolynomialEquiv D d a u hu).trans
    (MvPolynomial.mapEquiv (σ × ℕ) (deltaDivisionSecondCoefficientPowerEquiv D d a u))

/-- 第2通常δ剰余の両初期変数は同時根添加環の指定根。 -/
@[simp] theorem deltaDivisionSecondResiduePowerPolynomialEquiv_initial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (i : Fin 2) :
    deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.X (s, i.val))) =
      MvPolynomial.C (monicPowerFamilyRoot p (σ × Fin 2) _
        (fun z => Ideal.Quotient.mk _ (deltaDivisionTwoPowerCoefficients D d a u z)) (s, i)) := by
  change MvPolynomial.mapEquiv _ _
    (deltaDivisionSecondResiduePolynomialEquiv D d a u hu _) = _
  rw [deltaDivisionSecondResiduePolynomialEquiv_initial, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (deltaDivisionSecondCoefficientPowerEquiv_root D d a u (s, i))

/-- 第2通常δ剰余の後続変数は同時根添加環上の自由変数。 -/
@[simp] theorem deltaDivisionSecondResiduePowerPolynomialEquiv_tail
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (n : ℕ) :
    deltaDivisionSecondResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.X (s, n + 2))) =
      MvPolynomial.X (s, n) := by
  change MvPolynomial.mapEquiv _ _
    (deltaDivisionSecondResiduePolynomialEquiv D d a u hu _) = _
  rw [deltaDivisionSecondResiduePolynomialEquiv_tail, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_X]

end SerrePositivity.BhattScholze
