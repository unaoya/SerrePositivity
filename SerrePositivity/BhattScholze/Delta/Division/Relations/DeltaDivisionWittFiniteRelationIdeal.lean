module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionWittRelationIdeal
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSecondFinitePresentation

/-! # 実際の有限δ関係イデアルの全段Witt根生成元表示

既存の有限δイデアルと第一剰余イデアルを使い、後続式を反復する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 相対自由環の指定生成元に対応する、源の具体的Witt根関係元。 -/
def deltaDivisionRelativeWittRelationElement (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) : RelativeFreeDeltaRing (R := A) σ :=
  deltaDivisionWittRelationElement (relativeFreeDeltaStructure σ D) (MvPolynomial.C d)
    (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s))
    (u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)) n

/-- 深さ2からの初期N段のWitt根関係元族で生成した通常イデアル。 -/
def deltaDivisionFiniteWittRelationIdeal (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin N =>
    deltaDivisionRelativeWittRelationElement D d a u z.1 z.2.val)

/-- 零段のWitt根関係イデアルは零。 -/
@[simp] theorem deltaDivisionFiniteWittRelationIdeal_zero (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) : deltaDivisionFiniteWittRelationIdeal D d a u 0 = ⊥ := by
  apply le_bot_iff.mp
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, i⟩, rfl⟩
  exact Fin.elim0 i

/-- 初期Witt根関係イデアルは次の族を添加して得られる。 -/
theorem deltaDivisionFiniteWittRelationIdeal_succ (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    deltaDivisionFiniteWittRelationIdeal D d a u (N + 1) =
      deltaDivisionFiniteWittRelationIdeal D d a u N ⊔
        Ideal.span (Set.range fun s => deltaDivisionRelativeWittRelationElement D d a u s N) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    change deltaDivisionRelativeWittRelationElement D d a u s i.val ∈ _
    by_cases hi : i.val < N
    · apply (show deltaDivisionFiniteWittRelationIdeal D d a u N ≤ _ from le_sup_left)
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨i.val, hi⟩), rfl⟩)
    · have he : i.val = N := by omega
      rw [he]
      apply (show Ideal.span
          (Set.range fun s => deltaDivisionRelativeWittRelationElement D d a u s N) ≤
        deltaDivisionFiniteWittRelationIdeal D d a u N ⊔ _ from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, i⟩, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, i.castSucc), rfl⟩)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, Fin.last N), rfl⟩)

/-- 実際の有限δ関係イデアルの次段は、下位イデアルにWitt根関係元族を加えたもの。 -/
theorem deltaDivisionFiniteRelationIdeal_succ_witt (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (hp : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (n : ℕ) :
    Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      deltaDivisionFiniteRelationIdeal D d a (n + 2) =
    (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      deltaDivisionFiniteRelationIdeal D d a (n + 1)) ⊔
        Ideal.span (Set.range fun s => deltaDivisionRelativeWittRelationElement D d a u s n) := by
  let E := relativeFreeDeltaStructure σ D
  let I := Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
    deltaDivisionFiniteRelationIdeal D d a (n + 1)
  have hc : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤ I := le_sup_left
  have hr : deltaDivisionFiniteRelationIdeal D d a (n + 1) ≤ I := le_sup_right
  have hpI : (p : RelativeFreeDeltaRing (R := A) σ) ∈ I := hc (Ideal.subset_span (by simp))
  have hdI : MvPolynomial.C d ∈ I := hc (Ideal.subset_span (by simp))
  have hlow (s : σ) (i : ℕ) (hi : i ≤ n + 1) :
      E.delta^[i] (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) ∈ I := by
    apply hr
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨i, by omega⟩), rfl⟩)
  have hu' : ((u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ) :
      (RelativeFreeDeltaRing (R := A) σ)ˣ) : RelativeFreeDeltaRing (R := A) σ) =
        E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (u : A) = _
    rw [hu, relativeFreeDeltaStructure_delta_C]
  have he := deltaDivision_family_next_jets_sup_span_eq_witt_relations E hp hg I hpI
    (MvPolynomial.C d) (fun s => MvPolynomial.X (s, 0)) (fun s => MvPolynomial.C (a s))
    hdI (u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)) hu' n hlow
  rw [deltaDivisionFiniteRelationIdeal_succ D d a (n + 1), ← sup_assoc]
  exact he

/-- 全有限δ剰余イデアルは第一剰余イデアルと初期Witt根関係元族で生成される。 -/
theorem deltaDivisionFiniteRelationIdeal_eq_first_sup_witt (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (hp : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (N : ℕ) :
    Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      deltaDivisionFiniteRelationIdeal D d a (N + 1) =
        deltaDivisionFirstResidueIdeal D d a ⊔ deltaDivisionFiniteWittRelationIdeal D d a u N := by
  induction N with
  | zero => rw [deltaDivisionFiniteWittRelationIdeal_zero, sup_bot_eq]; rfl
  | succ N ih =>
      change Ideal.span _ ⊔ deltaDivisionFiniteRelationIdeal D d a (N + 2) = _
      rw [deltaDivisionFiniteRelationIdeal_succ_witt D d a u hu hp hg N, ih,
        deltaDivisionFiniteWittRelationIdeal_succ, sup_assoc]

end SerrePositivity.BhattScholze
