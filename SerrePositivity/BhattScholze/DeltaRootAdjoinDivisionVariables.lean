module

public import SerrePositivity.BhattScholze.DeltaRootAdjoinDivisionResidue

/-! # 根δ除算添加環の源変数のrank-one性と実際の根関係 -/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 既存rank-one多項式δ環の根関係をCdでδ除算した実際のraw環。 -/
abbrev DeltaRootAdjoinDivision :=
  DeltaAdjoinDivision (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b)

/-- raw環内の源多項式変数の標準δ係数像。 -/
def deltaRootAdjoinDivisionVariable (s : σ) : DeltaRootAdjoinDivision D d b :=
  deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b) (MvPolynomial.X s)

/-- raw環内の根変数のδ値は零。残余商のδ構造は仮定しない。 -/
theorem deltaRootAdjoinDivisionVariable_delta (s : σ) :
    (deltaAdjoinDivisionStructure (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b)).delta
        (deltaRootAdjoinDivisionVariable D d b s) = 0 := by
  have h := deltaAdjoinDivisionMap_isDeltaHom (polynomialRankOneDeltaStructure σ D)
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) (MvPolynomial.X s)
  rw [polynomialRankOneDeltaStructure_delta_X, map_zero] at h
  exact h.symm

/-- raw環内の根変数のp乗と指定元の像の差は、dの像と除算変数の積。 -/
theorem deltaRootAdjoinDivisionVariable_pow (s : σ) :
    deltaRootAdjoinDivisionVariable D d b s ^ p =
      deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s)) +
      deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) (MvPolynomial.C d) *
      deltaAdjoinDivisionVariable (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) s := by
  have h := deltaAdjoinDivision_relation (polynomialRankOneDeltaStructure σ D)
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) s
  change _ = deltaAdjoinDivisionMap _ _ _ (MvPolynomial.X s ^ p - MvPolynomial.C (b s)) at h
  rw [map_sub, map_pow] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- dの像を消す任意通常環射の先で、源変数の像は指定元のp乗根。 -/
theorem deltaRootAdjoinDivisionVariable_map_pow {T : Type w} [CommRing T]
    (q : DeltaRootAdjoinDivision D d b →+* T)
    (hd : q (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b) (MvPolynomial.C d)) = 0) (s : σ) :
    q (deltaRootAdjoinDivisionVariable D d b s) ^ p =
      q (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s))) := by
  have h := congrArg q (deltaRootAdjoinDivisionVariable_pow D d b s)
  simpa only [map_pow, map_add, map_mul, hd, zero_mul, add_zero] using h

end SerrePositivity.BhattScholze
