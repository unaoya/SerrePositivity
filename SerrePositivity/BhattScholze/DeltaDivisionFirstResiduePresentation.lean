module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteResidueRelation

/-! # 最初のδ除算剰余のモニック関係式表示

深さ0,1の通常イデアルを、係数関係式と初期変数のモニック冪関係式へ同定する。
全δ段・完備化・perfectionの平坦性は別工程。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 係数と初期モニック冪関係式で生成する通常イデアル。 -/
def deltaDivisionFirstMonicIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))

/-- 深さ0,1の通常イデアルを消すための具体的な判定。 -/
theorem deltaDivisionFirstResidueIdeal_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionFirstResidueIdeal D d a ≤ RingHom.ker q ↔
      q (p : RelativeFreeDeltaRing (R := A) σ) = 0 ∧ q (MvPolynomial.C d) = 0 ∧
        ∀ s, q (deltaDivisionIteratedRelation D d a s 0) = 0 ∧
          q (deltaDivisionIteratedRelation D d a s 1) = 0 := by
  constructor
  · intro h
    have hbase : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤
        deltaDivisionFirstResidueIdeal D d a := le_sup_left
    have hrel : deltaDivisionFiniteRelationIdeal D d a 1 ≤
        deltaDivisionFirstResidueIdeal D d a := le_sup_right
    refine ⟨h (hbase (Ideal.subset_span (by simp))),
      h (hbase (Ideal.subset_span (by simp))), fun s => ⟨?_, ?_⟩⟩
    · exact h (hrel (Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨0, by decide⟩), rfl⟩)))
    · exact h (hrel (Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨1, by decide⟩), rfl⟩)))
  · rintro ⟨hp, hd, hrel⟩
    apply sup_le
    · apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hp
      · exact hd
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, n⟩, rfl⟩
      change q (deltaDivisionIteratedRelation D d a s n.val) = 0
      have hn : n.val = 0 ∨ n.val = 1 := by omega
      rcases hn with hn | hn
      · simpa only [hn] using (hrel s).1
      · simpa only [hn] using (hrel s).2

/-- モニック表示の通常イデアルを消すための具体的な判定。 -/
theorem deltaDivisionFirstMonicIdeal_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionFirstMonicIdeal D d a u ≤ RingHom.ker q ↔
      q (p : RelativeFreeDeltaRing (R := A) σ) = 0 ∧ q (MvPolynomial.C d) = 0 ∧
        ∀ s, q (MvPolynomial.C (a s)) = 0 ∧
          (q (MvPolynomial.X (s, 0))) ^ p =
            q (MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) := by
  constructor
  · intro h
    have hb : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤
        deltaDivisionFirstMonicIdeal D d a u := le_sup_left.trans le_sup_left
    have ha : Ideal.span (Set.range fun s => MvPolynomial.C (a s)) ≤
        deltaDivisionFirstMonicIdeal D d a u := le_sup_right.trans le_sup_left
    have hm : Ideal.span (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) ≤
        deltaDivisionFirstMonicIdeal D d a u := le_sup_right
    refine ⟨h (hb (Ideal.subset_span (by simp))), h (hb (Ideal.subset_span (by simp))),
      fun s => ⟨h (ha (Ideal.subset_span (Set.mem_range_self s))), ?_⟩⟩
    have he := h (hm (Ideal.subset_span (Set.mem_range_self s)))
    change q (_ - _) = 0 at he
    simpa only [map_sub, map_pow, sub_eq_zero] using he
  · rintro ⟨hp, hd, hs⟩
    apply sup_le
    · apply sup_le
      · apply Ideal.span_le.mpr
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hp
        · exact hd
      · apply Ideal.span_le.mpr
        rintro _ ⟨s, rfl⟩
        exact (hs s).1
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      change q (_ - _) = 0
      rw [map_sub, map_pow, (hs s).2, sub_self]

/-- 元の低次イデアルとモニック表示イデアルは同じ通常射を消す。 -/
theorem deltaDivisionFirstResidue_monic_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionFirstResidueIdeal D d a ≤ RingHom.ker q ↔
      deltaDivisionFirstMonicIdeal D d a u ≤ RingHom.ker q := by
  rw [deltaDivisionFirstResidueIdeal_le_ker_iff, deltaDivisionFirstMonicIdeal_le_ker_iff]
  let f := q.comp (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)
  have hunit : ((u.map f : Bˣ) : B) =
      q ((relativeFreeDeltaStructure σ D).delta (MvPolynomial.C d)) := by
    change f (u : A) = _
    rw [hu, relativeFreeDeltaStructure_delta_C]
    rfl
  have hcoeff (s : σ) : (u.map f)⁻¹.val *
      q ((relativeFreeDeltaStructure σ D).delta (MvPolynomial.C (a s))) =
      q (MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) := by
    rw [relativeFreeDeltaStructure_delta_C, map_mul, map_mul]
    rfl
  constructor
  · rintro ⟨hp, hd, hs⟩
    refine ⟨hp, hd, fun s => ?_⟩
    have he := (deltaDivisionFirstRelations_vanish_iff (relativeFreeDeltaStructure σ D) q
      (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd
      (u.map f) hunit).mp (hs s)
    simpa only [hcoeff] using he
  · rintro ⟨hp, hd, hs⟩
    refine ⟨hp, hd, fun s => ?_⟩
    apply (deltaDivisionFirstRelations_vanish_iff (relativeFreeDeltaStructure σ D) q
      (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd
      (u.map f) hunit).mpr
    simpa only [hcoeff] using hs s

/-- 実際の低次通常イデアルは、係数関係式とモニック冪関係式のイデアル。 -/
theorem deltaDivisionFirstResidueIdeal_eq_monic
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    deltaDivisionFirstResidueIdeal D d a = deltaDivisionFirstMonicIdeal D d a u := by
  apply le_antisymm
  · have h : deltaDivisionFirstMonicIdeal D d a u ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionFirstMonicIdeal D d a u)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionFirstResidue_monic_le_ker_iff D d a u hu _).mpr h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)
  · have h : deltaDivisionFirstResidueIdeal D d a ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionFirstResidue_monic_le_ker_iff D d a u hu _).mp h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)

/-- 実際の低次商とモニック関係式商の標準同型。 -/
def deltaDivisionFirstResidueMonicEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstMonicIdeal D d a u) :=
  Ideal.quotEquivOfEq (deltaDivisionFirstResidueIdeal_eq_monic D d a u hu)

/-- 低次モニック商同型は標準商射と両立する。 -/
@[simp] theorem deltaDivisionFirstResidueMonicEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFirstResidueMonicEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) x) =
        Ideal.Quotient.mk (deltaDivisionFirstMonicIdeal D d a u) x :=
  Ideal.quotEquivOfEq_mk _ x

end SerrePositivity.BhattScholze
