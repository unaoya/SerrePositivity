module

public import SerrePositivity.BhattScholze.DeltaDivisionIteratedRelations

/-! # 実有限δ関係と自由δ射の有限評価関係

δ^n(u−v)とδ^n(u)−δ^n(v)は一般には等しくないが、全深さ≤Nで生成するイデアルは一致する。
この通常イデアル比較だけで導来基底変更の同定を主張しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem delta_span_to (D : DeltaStructure p A) (s : Set A) (J : Ideal A)
    (hle : Ideal.span s ≤ J) (hgen : ∀ x ∈ s, D.delta x ∈ J)
    {x : A} (hx : x ∈ Ideal.span s) : D.delta x ∈ J := by
  change x ∈ Submodule.span A s at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [D.delta_add]
      exact J.add_mem (J.add_mem ihx ihy) (DeltaStructure.additionCarry_mem J (hle hx) (hle hy))
  | smul r x hx ih =>
      change D.delta (r * x) ∈ J
      rw [D.delta_mul]
      exact J.add_mem (J.add_mem (J.mul_mem_left _ ih)
        (J.mul_mem_left _ (J.pow_mem_of_mem (hle hx) p (Fact.out : p.Prime).pos)))
        (J.mul_mem_left _ ih)

private theorem delta_sub_correction_mem (D : DeltaStructure p A) (J : Ideal A) (x y : A)
    (hxy : x - y ∈ J) : D.delta x - D.delta y - D.delta (x - y) ∈ J := by
  let q := Ideal.Quotient.mk J
  have hz : q (x - y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxy
  have hc : q ((WittVector.teichmuller p (x - y) + WittVector.teichmuller p y).coeff 1) = 0 := by
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hz, WittVector.teichmuller_zero, zero_add]
    simp
  have h := congrArg q (D.delta_add (x - y) y)
  rw [sub_add_cancel, map_add, map_add, hc, add_zero] at h
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (D.delta x - D.delta y - D.delta (x - y)) = 0
  rw [map_sub, map_sub, h]
  ring

private def pairEvaluationIdeal (D : DeltaStructure p A) (x y : σ → A) (N : ℕ) : Ideal A :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    D.delta^[z.2.val] (x z.1) - D.delta^[z.2.val] (y z.1))

private def pairDifferenceIdeal (D : DeltaStructure p A) (x y : σ → A) (N : ℕ) : Ideal A :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) => D.delta^[z.2.val] (x z.1 - y z.1))

private theorem pairEvaluationIdeal_mono (D : DeltaStructure p A) (x y : σ → A) :
    Monotone (pairEvaluationIdeal D x y) := by
  intro N M h
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, i⟩, rfl⟩
  exact Ideal.subset_span ⟨(s, ⟨i.val, by omega⟩), rfl⟩

private theorem pairDifferenceIdeal_mono (D : DeltaStructure p A) (x y : σ → A) :
    Monotone (pairDifferenceIdeal D x y) := by
  intro N M h
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, i⟩, rfl⟩
  exact Ideal.subset_span ⟨(s, ⟨i.val, by omega⟩), rfl⟩

private theorem pairDifferenceIdeal_delta (D : DeltaStructure p A) (x y : σ → A) (N : ℕ)
    {z : A} (hz : z ∈ pairDifferenceIdeal D x y N) :
    D.delta z ∈ pairDifferenceIdeal D x y (N + 1) := by
  apply delta_span_to D _ _ (pairDifferenceIdeal_mono D x y (Nat.le_succ N)) ?_ hz
  rintro _ ⟨⟨s, i⟩, rfl⟩
  apply Ideal.subset_span
  exact ⟨(s, ⟨i.val + 1, by omega⟩), Function.iterate_succ_apply' D.delta _ _⟩

private theorem pairEvaluationIdeal_delta (D : DeltaStructure p A) (x y : σ → A) (N : ℕ)
    {z : A} (hz : z ∈ pairEvaluationIdeal D x y N) :
    D.delta z ∈ pairEvaluationIdeal D x y (N + 1) := by
  apply delta_span_to D _ _ (pairEvaluationIdeal_mono D x y (Nat.le_succ N)) ?_ hz
  rintro _ ⟨⟨s, i⟩, rfl⟩
  have hmem : D.delta^[i.val] (x s) - D.delta^[i.val] (y s) ∈
      pairEvaluationIdeal D x y (N + 1) :=
    Ideal.subset_span ⟨(s, ⟨i.val, by omega⟩), rfl⟩
  have hnext : D.delta (D.delta^[i.val] (x s)) - D.delta (D.delta^[i.val] (y s)) ∈
      pairEvaluationIdeal D x y (N + 1) := by
    have hm : D.delta^[i.val + 1] (x s) - D.delta^[i.val + 1] (y s) ∈
        pairEvaluationIdeal D x y (N + 1) :=
      Ideal.subset_span ⟨(s, ⟨i.val + 1, by omega⟩), rfl⟩
    simpa only [Function.iterate_succ_apply'] using hm
  have hc := delta_sub_correction_mem D _ _ _ hmem
  convert (pairEvaluationIdeal D x y (N + 1)).sub_mem hnext hc using 1; abel

private theorem pairEvaluation_mem_difference (D : DeltaStructure p A) (x y : σ → A)
    (s : σ) (N : ℕ) :
    D.delta^[N] (x s) - D.delta^[N] (y s) ∈ pairDifferenceIdeal D x y N := by
  induction N with
  | zero => exact Ideal.subset_span ⟨(s, 0), rfl⟩
  | succ N ih =>
      have hd := pairDifferenceIdeal_delta D x y N ih
      have hi := pairDifferenceIdeal_mono D x y (Nat.le_succ N) ih
      have hc := delta_sub_correction_mem D _ _ _ hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      convert (pairDifferenceIdeal D x y (N + 1)).add_mem hc hd using 1; abel

private theorem pairDifference_mem_evaluation (D : DeltaStructure p A) (x y : σ → A)
    (s : σ) (N : ℕ) :
    D.delta^[N] (x s - y s) ∈ pairEvaluationIdeal D x y N := by
  induction N with
  | zero => exact Ideal.subset_span ⟨(s, 0), rfl⟩
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      exact pairEvaluationIdeal_delta D x y N ih

private theorem pairIdeals_eq (D : DeltaStructure p A) (x y : σ → A) (N : ℕ) :
    pairEvaluationIdeal D x y N = pairDifferenceIdeal D x y N := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact pairDifferenceIdeal_mono D x y (by omega : i.val ≤ N)
      (pairEvaluation_mem_difference D x y s i.val)
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact pairEvaluationIdeal_mono D x y (by omega : i.val ≤ N)
      (pairDifference_mem_evaluation D x y s i.val)

/-- 自由δ射の座標評価から生じる深さnの実除算関係。 -/
def deltaDivisionEvaluationRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) : RelativeFreeDeltaRing (R := A) σ :=
  (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0)) -
    (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C (a s))

/-- 評価関係の定数側は、基底δ環の実反復δ座標の係数像。 -/
theorem deltaDivisionEvaluationRelation_eq (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) :
    deltaDivisionEvaluationRelation D d a s n =
      (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0)) -
        MvPolynomial.C (D.delta^[n] (a s)) := by
  have hc : ∀ k : ℕ, (relativeFreeDeltaStructure σ D).delta^[k] (MvPolynomial.C (a s)) =
      MvPolynomial.C (D.delta^[k] (a s)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        relativeFreeDeltaStructure_delta_C]
  exact congrArg (fun z =>
    (relativeFreeDeltaStructure σ D).delta^[n]
      (MvPolynomial.C d * MvPolynomial.X (s, 0)) - z) (hc n)

/-- 自由δ射の全深さ≤Nの評価関係で生成した実通常イデアル。 -/
def deltaDivisionFiniteEvaluationIdeal (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    deltaDivisionEvaluationRelation D d a z.1 z.2.val)

/-- 全有限段で、自由δ射の評価関係と既存の実反復差関係が同じイデアルを生成する。 -/
theorem deltaDivisionFiniteEvaluationIdeal_eq (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) :
    deltaDivisionFiniteEvaluationIdeal D d a N = deltaDivisionFiniteRelationIdeal D d a N := by
  exact pairIdeals_eq (relativeFreeDeltaStructure σ D)
    (fun s => MvPolynomial.C d * MvPolynomial.X (s, 0)) (fun s => MvPolynomial.C (a s)) N

/-- 各評価関係は既存の実有限段イデアルに属する。 -/
theorem deltaDivisionEvaluationRelation_mem_finite (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n N : ℕ) (hn : n ≤ N) :
    deltaDivisionEvaluationRelation D d a s n ∈ deltaDivisionFiniteRelationIdeal D d a N := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  exact Ideal.subset_span ⟨(s, ⟨n, by omega⟩), rfl⟩

/-- 自由δ射の全評価関係は、実raw δ除算包の標準商射で零となる。 -/
theorem deltaDivisionEvaluationRelation_quotient_eq_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
      (deltaDivisionRelationIdeal d a)) (deltaDivisionEvaluationRelation D d a s n) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  exact (le_iSup (deltaDivisionFiniteRelationIdeal D d a) n)
    (deltaDivisionEvaluationRelation_mem_finite D d a s n n le_rfl)

end SerrePositivity.BhattScholze
