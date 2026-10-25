module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionNormalizedDirectLimitEvaluation

/-! # 全段評価射の核と具体的正規化関係イデアル -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 無限相対自由環の任意多項式は有限初期変数の標準包含像。 -/
theorem relativeFreePolynomial_exists_finite_initial (f : RelativeFreeDeltaRing (R := A) σ) :
    ∃ N, ∃ g : MvPolynomial (σ × Fin (N + 1)) A,
      relativeFreeFiniteInitialPolynomialMap (N + 1) σ A g = f := by
  classical
  let N := f.vars.sup (fun z => z.2)
  have hfi : Function.Injective (fun z : σ × Fin (N + 1) => (z.1, z.2.val)) := by
    intro x y h
    exact Prod.ext (congrArg (fun z : σ × ℕ => z.1) h)
      (Fin.ext (congrArg (fun z : σ × ℕ => z.2) h))
  have hvars : (f.vars : Set (σ × ℕ)) ⊆
      Set.range (fun z : σ × Fin (N + 1) => (z.1, z.2.val)) := by
    intro z hz
    have hle : z.2 ≤ N := Finset.le_sup hz
    exact ⟨(z.1, ⟨z.2, Nat.lt_succ_of_le hle⟩), rfl⟩
  obtain ⟨g, hg⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range f _ hfi hvars
  exact ⟨N, g, hg⟩

/-- 有限初期多項式の評価が零であることは、実際の有限表示イデアルへの所属。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
    (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) = 0 ↔
      f ∈ deltaDivisionFiniteNormalizedPresentationIdeal D d a u N := by
  rw [deltaDivisionNormalizedDirectLimitEvaluation_initial]
  constructor
  · intro h
    have hz : Ideal.Quotient.mk (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) f = 0 :=
      deltaDivisionFiniteNormalizedDirectLimitOf_injective D d a u N
        (h.trans (map_zero (deltaDivisionFiniteNormalizedDirectLimitOf D d a u N)).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- 全段評価射の核を有限初期環に戻したイデアルは、その段の表示イデアル。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_ker_comap_initial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.comap (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
      (RingHom.ker (deltaDivisionNormalizedDirectLimitEvaluation D d a u)) =
      deltaDivisionFiniteNormalizedPresentationIdeal D d a u N := by
  ext f
  change deltaDivisionNormalizedDirectLimitEvaluation D d a u
    (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) = 0 ↔ _
  exact deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff D d a u N f

/-- 各有限表示イデアルの包含像の和で得られる具体的全段関係イデアル。 -/
def deltaDivisionInfiniteNormalizedPresentationIdeal (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  ⨆ N : ℕ, Ideal.map (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
    (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N)

/-- 全段評価射の核は、具体的全段正規化関係イデアルに一致する。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_ker_eq_infinite_normalized
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    RingHom.ker (deltaDivisionNormalizedDirectLimitEvaluation D d a u) =
      deltaDivisionInfiniteNormalizedPresentationIdeal D d a u := by
  unfold deltaDivisionInfiniteNormalizedPresentationIdeal
  apply le_antisymm
  · intro f hf
    change deltaDivisionNormalizedDirectLimitEvaluation D d a u f = 0 at hf
    obtain ⟨N, g, rfl⟩ := relativeFreePolynomial_exists_finite_initial f
    have hg := (deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff
      D d a u N g).mp hf
    apply (show Ideal.map (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
        (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ≤ _ from
        le_iSup (fun n : ℕ =>
          Ideal.map (relativeFreeFiniteInitialPolynomialMap (n + 1) σ A).toRingHom
            (deltaDivisionFiniteNormalizedPresentationIdeal D d a u n)) N)
    exact Ideal.mem_map_of_mem _ hg
  · apply iSup_le
    intro N
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    change deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A g) = 0
    exact (deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff D d a u N g).mpr hg

/-- 具体的全段正規化関係イデアルの商は、構成した全段環に同型。 -/
def deltaDivisionNormalizedDirectLimitQuotientEquiv (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      deltaDivisionInfiniteNormalizedPresentationIdeal D d a u) ≃+*
      DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (Ideal.quotEquivOfEq
    (deltaDivisionNormalizedDirectLimitEvaluation_ker_eq_infinite_normalized D d a u).symm).trans
    ((deltaDivisionNormalizedDirectLimitEvaluation D d a u).quotientKerEquivOfSurjective
      (deltaDivisionNormalizedDirectLimitEvaluation_surjective D d a u))

/-- 全段商表示同型は、元の無限自由環の標準商射を具体的評価射へ送る。 -/
theorem deltaDivisionNormalizedDirectLimitQuotientEquiv_mk (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u (Ideal.Quotient.mk _ f) =
      deltaDivisionNormalizedDirectLimitEvaluation D d a u f := by
  rw [deltaDivisionNormalizedDirectLimitQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- 全段商表示同型は、基底係数の標準商像を全段係数射へ送る。 -/
theorem deltaDivisionNormalizedDirectLimitQuotientEquiv_C (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
      deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) := by
  rw [deltaDivisionNormalizedDirectLimitQuotientEquiv_mk,
    deltaDivisionNormalizedDirectLimitEvaluation_C]

end SerrePositivity.BhattScholze
