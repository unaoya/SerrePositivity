module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivision

/-! # δ除算包の全反復関係式

δ閉包を、元の指定生成元の反復δ像だけによる通常イデアルとして表示する。
δ除算包の全段の関係式と変数を具体化する。三角形の次数評価は別工程。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

variable {σ : Type v}

/-- δ除算包の指定した全反復関係式。 -/
def deltaDivisionIteratedRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) : RelativeFreeDeltaRing (R := A) σ :=
  (relativeFreeDeltaStructure σ D).delta^[n]
    (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))

/-- δ除算包の定義イデアルは、指定関係式の全反復δ像で生成される。 -/
theorem deltaDivision_deltaClosure_eq_span_iteratedRelations
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) =
      Ideal.span (Set.range fun z : σ × ℕ => deltaDivisionIteratedRelation D d a z.1 z.2) := by
  rw [deltaDivisionRelationIdeal,
    DeltaStructure.deltaClosure_span_eq_span_generator_iterates]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨n, _, ⟨s, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨(s, n), rfl⟩
  · rintro ⟨⟨s, n⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, _, ⟨s, rfl⟩, rfl⟩

/-- 全反復関係式は実際のδ除算包で零になる。 -/
theorem deltaDivisionIteratedRelation_quotient_eq_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
      (deltaDivisionRelationIdeal d a)) (deltaDivisionIteratedRelation D d a s n) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [deltaDivision_deltaClosure_eq_span_iteratedRelations]
  exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, n), rfl⟩)

/-- 相対自由δ環の反復δ変数は、全段の指定多項式変数と一致する。 -/
theorem relativeFreeDeltaStructure_iterate_delta_X
    (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.X (s, 0)) =
      MvPolynomial.X (s, n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, relativeFreeDeltaStructure_delta_X]

/-- 実際のδ除算包の初期変数の反復δ像は、全段変数の標準商像。 -/
theorem deltaAdjoinDivisionVariable_iterate_delta
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    (deltaAdjoinDivisionStructure D d a).delta^[n] (deltaAdjoinDivisionVariable D d a s) =
      Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a)) (MvPolynomial.X (s, n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact ((relativeFreeDeltaStructure σ D).isDeltaHom_quotient_mk _
        ((relativeFreeDeltaStructure σ D).isStable_deltaClosure _)
        (MvPolynomial.X (s, n))).symm.trans
          (congrArg (Ideal.Quotient.mk _) (relativeFreeDeltaStructure_delta_X σ D s n))

/-- 全反復関係式を消す通常の環射は、定義イデアル全体を消す。 -/
theorem deltaDivisionIteratedRelations_kill_ideal
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    ∀ x ∈ (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a),
      f x = 0 := by
  have hle : (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) ≤
      RingHom.ker f := by
    rw [deltaDivision_deltaClosure_eq_span_iteratedRelations]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    exact hf s n
  exact fun x hx => hle hx

/-- 全反復関係式を消す通常の環射から、δ除算包上の具体的な環射を構成する。
終域のδ構造を仮定しない。 -/
def deltaDivisionIteratedRelationsLift
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    DeltaAdjoinDivision D d a →+* B :=
  Ideal.Quotient.lift _ f (deltaDivisionIteratedRelations_kill_ideal D d a f hf)

/-- 全関係式から構成した射と標準商射の図式。 -/
theorem deltaDivisionIteratedRelationsLift_comp_mk
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    (deltaDivisionIteratedRelationsLift D d a f hf).comp
      (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = f := rfl

/-- 全反復関係式を消す通常の環射は、δ除算包へ一意に降りる。 -/
theorem existsUnique_deltaDivisionIteratedRelationsLift
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    ∃! L : DeltaAdjoinDivision D d a →+* B,
      L.comp (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = f := by
  refine ⟨deltaDivisionIteratedRelationsLift D d a f hf, rfl, ?_⟩
  intro L hL
  exact Ideal.Quotient.ringHom_ext hL

/-- 深さN以下の反復関係式で生成した通常イデアル。
添字族σの有限性は仮定しない。 -/
def deltaDivisionFiniteRelationIdeal (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    deltaDivisionIteratedRelation D d a z.1 z.2.val)

/-- 反復関係式の有限深さのイデアルは単調に増大する。 -/
theorem deltaDivisionFiniteRelationIdeal_mono
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    Monotone (deltaDivisionFiniteRelationIdeal D d a) := by
  intro N M hNM
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  apply Ideal.subset_span
  exact Set.mem_range.mpr ⟨(s, ⟨n.val, lt_of_lt_of_le n.isLt (Nat.add_le_add_right hNM 1)⟩), rfl⟩

/-- 実際のδ閉包は、有限深さの関係式イデアルの上限。 -/
theorem deltaDivision_deltaClosure_eq_iSup_finiteRelations
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) =
      ⨆ N, deltaDivisionFiniteRelationIdeal D d a N := by
  rw [deltaDivision_deltaClosure_eq_span_iteratedRelations]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    apply (le_iSup (deltaDivisionFiniteRelationIdeal D d a) n)
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨n, Nat.lt_succ_self n⟩), rfl⟩)
  · apply iSup_le
    intro N
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, n.val), rfl⟩)

end SerrePositivity.BhattScholze
