module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSecondFinitePresentation
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFirstResiduePresentation

/-! # 第2通常δ剰余のモニック関係式イデアル

実際の第2剰余イデアルを二つのモニック冪方程式のイデアルへ同定する。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 次のδ変数のモニック冪方程式の係数。基底δデータだけで表す。 -/
def deltaDivisionSecondPowerCoefficient (D : DeltaStructure p A) (a : σ → A) (d : A)
    (u : Aˣ) (s : σ) : A :=
  ((u⁻¹ : Aˣ) : A) ^ p * (D.delta (D.delta (a s)) - D.delta (D.delta d) *
    (((u⁻¹ : Aˣ) : A) * D.delta (a s)) ^ p)

/-- 初期モニックイデアルに次のモニック方程式を加えた通常イデアル。 -/
def deltaDivisionSecondMonicIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  deltaDivisionFirstMonicIdeal D d a u ⊔ Ideal.span (Set.range fun s =>
    MvPolynomial.X (s, 1) ^ p - MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s))

/-- 初期関係式を消す通常射について、第2関係式と次の冪方程式は同値。 -/
theorem deltaDivisionSecondIteratedRelation_vanish_iff_root
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hp : q (p : RelativeFreeDeltaRing (R := A) σ) = 0) (hd : q (MvPolynomial.C d) = 0)
    (s : σ) (h0 : q (deltaDivisionIteratedRelation D d a s 0) = 0)
    (h1 : q (deltaDivisionIteratedRelation D d a s 1) = 0) :
    q (deltaDivisionIteratedRelation D d a s 2) = 0 ↔
      q (MvPolynomial.X (s, 1)) ^ p =
        q (MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s)) := by
  let F := relativeFreeDeltaStructure σ D
  let f := q.comp (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)
  have hunit : ((u.map f : Bˣ) : B) = q (F.delta (MvPolynomial.C d)) := by
    change f (u : A) = _
    rw [hu, relativeFreeDeltaStructure_delta_C]
    rfl
  have hpow := deltaDivisionFirstRelation_pow_of_vanishing F q (MvPolynomial.C d)
    (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd h0 h1 (u.map f) hunit
  have he := deltaDivisionSecondRelation_vanish_iff_pow F q (MvPolynomial.C d)
    (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd h0 h1 (u.map f) hunit
  rw [pow_mul, hpow] at he
  have hcoeff : ((u.map f)⁻¹ : Bˣ) ^ p *
      (q (F.delta (F.delta (MvPolynomial.C (a s)))) -
        q (F.delta (F.delta (MvPolynomial.C d))) *
          (((u.map f)⁻¹ : Bˣ) * q (F.delta (MvPolynomial.C (a s)))) ^ p) =
      q (MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s)) := by
    simp only [F, relativeFreeDeltaStructure_delta_C, deltaDivisionSecondPowerCoefficient,
      map_mul, map_pow, map_sub]
    rfl
  rw [hcoeff] at he
  simpa only [F, deltaDivisionIteratedRelation, Function.iterate_succ_apply',
    Function.iterate_zero_apply, relativeFreeDeltaStructure_delta_X, Nat.zero_add] using he

/-- 第2通常剰余イデアルと二段のモニックイデアルは同じ通常射を消す。 -/
theorem deltaDivisionSecondResidue_monic_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionSecondResidueIdeal D d a ≤ RingHom.ker q ↔
      deltaDivisionSecondMonicIdeal D d a u ≤ RingHom.ker q := by
  rw [deltaDivisionSecondResidueIdeal_eq_first_sup, deltaDivisionSecondMonicIdeal,
    ← deltaDivisionFirstResidueIdeal_eq_monic D d a u hu, sup_le_iff, sup_le_iff]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    obtain ⟨hp, hd, h01⟩ := (deltaDivisionFirstResidueIdeal_le_ker_iff D d a q).mp hfirst
    refine ⟨hfirst, Ideal.span_le.mpr ?_⟩
    rintro _ ⟨s, rfl⟩
    have h2 : q (deltaDivisionIteratedRelation D d a s 2) = 0 :=
      hsecond (Ideal.subset_span (Set.mem_range_self s))
    have hpow := (deltaDivisionSecondIteratedRelation_vanish_iff_root D d a u hu q hp hd s
      (h01 s).1 (h01 s).2).mp h2
    change q (_ - _) = 0
    rw [map_sub, map_pow, hpow, sub_self]
  · rintro ⟨hfirst, hsecond⟩
    obtain ⟨hp, hd, h01⟩ := (deltaDivisionFirstResidueIdeal_le_ker_iff D d a q).mp hfirst
    refine ⟨hfirst, Ideal.span_le.mpr ?_⟩
    rintro _ ⟨s, rfl⟩
    have hm := hsecond (Ideal.subset_span (Set.mem_range_self s))
    change q (_ - _) = 0 at hm
    have hpow : q (MvPolynomial.X (s, 1)) ^ p =
        q (MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s)) := by
      simpa only [map_sub, map_pow, sub_eq_zero] using hm
    exact (deltaDivisionSecondIteratedRelation_vanish_iff_root D d a u hu q hp hd s
      (h01 s).1 (h01 s).2).mpr hpow

/-- 実際の第2剰余イデアルは二つのモニック冪関係式の通常イデアル。 -/
theorem deltaDivisionSecondResidueIdeal_eq_monic
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    deltaDivisionSecondResidueIdeal D d a = deltaDivisionSecondMonicIdeal D d a u := by
  apply le_antisymm
  · have h : deltaDivisionSecondMonicIdeal D d a u ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionSecondMonicIdeal D d a u)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionSecondResidue_monic_le_ker_iff D d a u hu _).mpr h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)
  · have h : deltaDivisionSecondResidueIdeal D d a ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionSecondResidue_monic_le_ker_iff D d a u hu _).mp h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)

/-- 実際の第2通常商と二段のモニック関係式商の標準同型。 -/
def deltaDivisionSecondResidueMonicEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondMonicIdeal D d a u) :=
  Ideal.quotEquivOfEq (deltaDivisionSecondResidueIdeal_eq_monic D d a u hu)

/-- 二段のモニック商同型は標準商射と両立する。 -/
@[simp] theorem deltaDivisionSecondResidueMonicEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionSecondResidueMonicEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) x) =
      Ideal.Quotient.mk (deltaDivisionSecondMonicIdeal D d a u) x :=
  Ideal.quotEquivOfEq_mk _ x

end SerrePositivity.BhattScholze
