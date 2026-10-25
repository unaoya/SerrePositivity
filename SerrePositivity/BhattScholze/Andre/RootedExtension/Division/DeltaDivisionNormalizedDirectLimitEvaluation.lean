module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteNormalizedDirectLimitAlgebra

/-! # 無限相対自由多項式環から全段正規化環への具体的評価射 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 第n変数は、その変数を含む第n有限段の標準商像として全段環に置く。 -/
def deltaDivisionNormalizedDirectLimitVariable (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  deltaDivisionFiniteNormalizedDirectLimitOf D d a u n
    (Ideal.Quotient.mk _ (MvPolynomial.X (s, Fin.last n)))

/-- 同じ変数の任意後段での標準商像は最初の像と一致する。 -/
theorem deltaDivisionNormalizedDirectLimitVariable_at_stage (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) {n N : ℕ} (h : n ≤ N) :
    deltaDivisionNormalizedDirectLimitVariable D d a u s n =
      deltaDivisionFiniteNormalizedDirectLimitOf D d a u N
        (Ideal.Quotient.mk _ (MvPolynomial.X (s, (⟨n, by omega⟩ : Fin (N + 1))))) := by
  have he := deltaDivisionFiniteNormalizedDirectLimitOf_compatible D d a u h
    (Ideal.Quotient.mk _ (MvPolynomial.X (s, Fin.last n)))
  rw [deltaDivisionFiniteNormalizedTowerMap_mk] at he
  have hi : (Fin.last n).castLE (Nat.succ_le_succ h) =
      (⟨n, by omega⟩ : Fin (N + 1)) := Fin.ext rfl
  simpa [deltaDivisionNormalizedDirectLimitVariable,
    deltaDivisionFiniteNormalizedTowerInclusion, hi] using he.symm

/-- 基底係数と各変数の具体的像による、無限相対自由環から全段環への射。 -/
def deltaDivisionNormalizedDirectLimitEvaluation (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    RelativeFreeDeltaRing (R := A) σ →+* DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  MvPolynomial.eval₂Hom
    ((deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u).comp
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) d a)))
    (fun z => deltaDivisionNormalizedDirectLimitVariable D d a u z.1 z.2)

/-- 評価射は基底係数を適切な共通係数商の像へ送る。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_C (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    deltaDivisionNormalizedDirectLimitEvaluation D d a u (MvPolynomial.C b) =
      deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) :=
  MvPolynomial.eval₂Hom_C _ _ b

/-- 評価射は各自由変数を指定した全段像へ送る。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_X (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    deltaDivisionNormalizedDirectLimitEvaluation D d a u (MvPolynomial.X (s, n)) =
      deltaDivisionNormalizedDirectLimitVariable D d a u s n :=
  MvPolynomial.eval₂Hom_X' _ _ (s, n)

/-- 評価射の有限初期環への制限は、その段の標準商射と全段への射の合成。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_comp_initial (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    (deltaDivisionNormalizedDirectLimitEvaluation D d a u).comp
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom =
      (deltaDivisionFiniteNormalizedDirectLimitOf D d a u N).comp
        (Ideal.Quotient.mk (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    have hc : relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.C b) =
        MvPolynomial.C b := AlgHom.commutes _ b
    change deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.C b)) = _
    rw [hc, deltaDivisionNormalizedDirectLimitEvaluation_C,
      deltaDivisionFiniteNormalizedDirectLimitBaseMap_mk D d a u N]
    rfl
  · intro z
    have hx : relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.X z) =
        MvPolynomial.X (z.1, z.2.val) := by
      simp [relativeFreeFiniteInitialPolynomialMap]
    change deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.X z)) = _
    rw [hx, deltaDivisionNormalizedDirectLimitEvaluation_X]
    exact deltaDivisionNormalizedDirectLimitVariable_at_stage D d a u z.1
      (Nat.le_of_lt_succ z.2.isLt)

/-- 有限段の任意多項式についての標準商射図式。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_initial (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) =
      deltaDivisionFiniteNormalizedDirectLimitOf D d a u N (Ideal.Quotient.mk _ f) :=
  RingHom.congr_fun (deltaDivisionNormalizedDirectLimitEvaluation_comp_initial D d a u N) f

/-- 無限相対自由環から全段正規化環への具体的評価射は全射。 -/
theorem deltaDivisionNormalizedDirectLimitEvaluation_surjective (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    Function.Surjective (deltaDivisionNormalizedDirectLimitEvaluation D d a u) := by
  intro y
  obtain ⟨N, x, hx⟩ := deltaDivisionFiniteNormalizedDirectLimit_exists_stage D d a u y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f,
    (deltaDivisionNormalizedDirectLimitEvaluation_initial D d a u N f).trans hx⟩

end SerrePositivity.BhattScholze
