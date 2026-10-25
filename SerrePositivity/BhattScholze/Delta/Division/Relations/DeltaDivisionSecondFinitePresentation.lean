module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSecondFiniteResidueRelation

/-! # 第2有限段の関係式消滅の逆向き比較と実際の商

有限深さの商のδ安定性を要求せず、二つのモニック方程式を比較する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 最初の二つの関係式が消える場合、第2δ関係式と次の冪方程式は同値。 -/
theorem deltaDivisionSecondRelation_vanish_iff_pow
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (h0 : q (d * x - a) = 0) (h1 : q (D.delta (d * x - a)) = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    q (D.delta (D.delta (d * x - a))) = 0 ↔
      q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
        (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) * (q x) ^ (p * p)) := by
  constructor
  · intro h2
    exact deltaDivisionSecondRelation_pow_of_vanishing D q d x a hp hd h0 h1 h2 u hu
  · intro hpow
    have ha : q a = 0 := by
      simpa only [map_sub, map_mul, hd, zero_mul, zero_sub, neg_eq_zero] using h0
    have he := D.map_delta_delta_add_of_zero q hp (d * x - a) a h0 ha h1
    rw [sub_add_cancel] at he
    have hinv : (u : B) ^ p * ((u⁻¹ : Bˣ) : B) ^ p = 1 := by
      rw [← mul_pow]
      simp
    have hda : q (D.delta (D.delta (d * x))) = q (D.delta (D.delta a)) := by
      rw [delta_delta_mul_residue D d x q hp hd, ← hu, hpow, ← mul_assoc, hinv, one_mul]
      ring
    rw [he] at hda
    exact add_right_cancel (hda.trans (zero_add _).symm)

/-- 三つの低次関係式の消滅は、係数の消滅と二つのモニック方程式に同値。 -/
theorem deltaDivisionThreeRelations_vanish_iff
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    (q (d * x - a) = 0 ∧ q (D.delta (d * x - a)) = 0 ∧
      q (D.delta (D.delta (d * x - a))) = 0) ↔
    (q a = 0 ∧ (q x) ^ p = (u⁻¹ : Bˣ) * q (D.delta a) ∧
      q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
        (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) *
          (((u⁻¹ : Bˣ) : B) * q (D.delta a)) ^ p)) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have he := (deltaDivisionFirstRelations_vanish_iff D q d x a hp hd u hu).mp ⟨h0, h1⟩
    exact ⟨he.1, he.2,
      deltaDivisionSecondRelation_pow_constant_of_vanishing D q d x a hp hd h0 h1 h2 u hu⟩
  · rintro ⟨ha, hpow0, hpow1⟩
    have he := (deltaDivisionFirstRelations_vanish_iff D q d x a hp hd u hu).mpr ⟨ha, hpow0⟩
    refine ⟨he.1, he.2, ?_⟩
    apply (deltaDivisionSecondRelation_vanish_iff_pow D q d x a hp hd he.1 he.2 u hu).mpr
    simpa only [pow_mul, hpow0] using hpow1

variable {σ : Type w}

/-- 有限深さの関係式イデアルは次の段の関係式を添加して得られる。
任意Nに対する通常イデアルの等式であり、δ安定性は要求しない。 -/
theorem deltaDivisionFiniteRelationIdeal_succ
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    deltaDivisionFiniteRelationIdeal D d a (N + 1) =
      deltaDivisionFiniteRelationIdeal D d a N ⊔
        Ideal.span (Set.range fun s => deltaDivisionIteratedRelation D d a s (N + 1)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    change deltaDivisionIteratedRelation D d a s n.val ∈ _
    by_cases hn : n.val < N + 1
    · apply (show deltaDivisionFiniteRelationIdeal D d a N ≤
        deltaDivisionFiniteRelationIdeal D d a N ⊔ _ from le_sup_left)
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨n.val, hn⟩), rfl⟩)
    · have he : n.val = N + 1 := by omega
      rw [he]
      apply (show Ideal.span (Set.range fun t => deltaDivisionIteratedRelation D d a t (N + 1)) ≤
        deltaDivisionFiniteRelationIdeal D d a N ⊔ _ from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
  · apply sup_le
    · exact deltaDivisionFiniteRelationIdeal_mono D d a (Nat.le_succ N)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨N + 1, Nat.lt_succ_self _⟩), rfl⟩)

/-- p,dと深さ2以下のδ関係式を課した実際の通常イデアル。 -/
def deltaDivisionSecondResidueIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) :
    Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
    deltaDivisionFiniteRelationIdeal D d a 2

/-- 実際の第2通常商で、次の変数は基底データで指定したp乗根となる。 -/
theorem deltaDivisionSecondResidueQuotient_root_pow
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d) (s : σ) :
    let q := Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a)
    q (MvPolynomial.X (s, 1)) ^ p = q (MvPolynomial.C
      (((u⁻¹ : Aˣ) : A) ^ p * (D.delta (D.delta (a s)) - D.delta (D.delta d) *
        (((u⁻¹ : Aˣ) : A) * D.delta (a s)) ^ p))) := by
  let J := deltaDivisionSecondResidueIdeal D d a
  let q := Ideal.Quotient.mk J
  let f := q.comp (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)
  have hbase : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤ J :=
    le_sup_left
  have hp : q (p : RelativeFreeDeltaRing (R := A) σ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hbase (Ideal.subset_span (by simp)))
  have hd : q (MvPolynomial.C d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hbase (Ideal.subset_span (by simp)))
  have hrel : ∀ t n, n ≤ 2 → q (deltaDivisionIteratedRelation D d a t n) = 0 := by
    intro t n hn
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (show deltaDivisionFiniteRelationIdeal D d a 2 ≤ J from le_sup_right)
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(t, ⟨n, Nat.lt_succ_of_le hn⟩), rfl⟩)
  have hunit : ((u.map f : (RelativeFreeDeltaRing (R := A) σ ⧸ J)ˣ) :
      RelativeFreeDeltaRing (R := A) σ ⧸ J) = q (MvPolynomial.C (D.delta d)) := by
    change f (u : A) = _
    rw [hu]
    rfl
  have he := deltaDivisionFiniteSecondRoot_pow D d a q hp hd hrel (u.map f) hunit s
  change _ = f _
  rw [map_mul, map_pow, map_sub, map_mul, map_pow, map_mul]
  exact he

/-- 実際の第2剰余イデアルは初期剰余イデアルに第2関係式を加えたもの。 -/
theorem deltaDivisionSecondResidueIdeal_eq_first_sup
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    deltaDivisionSecondResidueIdeal D d a = deltaDivisionFirstResidueIdeal D d a ⊔
      Ideal.span (Set.range fun s => deltaDivisionIteratedRelation D d a s 2) := by
  change Ideal.span _ ⊔ deltaDivisionFiniteRelationIdeal D d a (1 + 1) = _
  rw [deltaDivisionFiniteRelationIdeal_succ, ← sup_assoc]
  rfl

end SerrePositivity.BhattScholze
