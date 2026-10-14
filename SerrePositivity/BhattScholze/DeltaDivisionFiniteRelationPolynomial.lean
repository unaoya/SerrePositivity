module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaStep
public import SerrePositivity.BhattScholze.DeltaDivisionIteratedRelations

/-! # 全反復δ除算関係式の具体的な有限多項式表示

有限δ計算を反復し、深さnの関係式を初期n+1段に置く。
この段数制御だけからモニック性・平坦性は結論しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 反復除算関係式を有限初期段で再帰的に計算した多項式。 -/
def deltaDivisionFiniteRelationPolynomial (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) : (n : ℕ) → MvPolynomial (σ × Fin (n + 1)) A
  | 0 => MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)
  | n + 1 => relativeFreeFiniteDeltaStep n σ D (deltaDivisionFiniteRelationPolynomial D d a s n)

/-- 深さ0の有限関係式は元の通常除算関係式。 -/
@[simp] theorem deltaDivisionFiniteRelationPolynomial_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) :
    deltaDivisionFiniteRelationPolynomial D d a s 0 =
      MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s) := rfl

/-- 次の有限関係式は、一段大きい有限環でのδ計算。 -/
@[simp] theorem deltaDivisionFiniteRelationPolynomial_succ
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionFiniteRelationPolynomial D d a s (n + 1) =
      relativeFreeFiniteDeltaStep n σ D (deltaDivisionFiniteRelationPolynomial D d a s n) := rfl

/-- 有限多項式の標準包含の像は、実際の全反復δ除算関係式に一致する。 -/
theorem deltaDivisionFiniteRelationPolynomial_image
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
      (deltaDivisionFiniteRelationPolynomial D d a s n) =
      deltaDivisionIteratedRelation D d a s n := by
  induction n with
  | zero =>
      simp [deltaDivisionFiniteRelationPolynomial, relativeFreeFiniteInitialPolynomialMap,
        deltaDivisionIteratedRelation]
  | succ n ih =>
      rw [deltaDivisionFiniteRelationPolynomial_succ,
        ← relativeFreeFiniteDeltaStep_delta_image, ih]
      exact (Function.iterate_succ_apply' (relativeFreeDeltaStructure σ D).delta n _).symm

/-- 深さnの実際の反復関係式には第n段までの変数しか現れない。 -/
theorem deltaDivisionIteratedRelation_variable_bound
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ)
    (z : σ × ℕ) (hz : z ∈ (deltaDivisionIteratedRelation D d a s n).vars) : z.2 ≤ n := by
  rw [← deltaDivisionFiniteRelationPolynomial_image D d a s n] at hz
  change z ∈ (MvPolynomial.rename (fun x : σ × Fin (n + 1) => (x.1, x.2.val))
    (deltaDivisionFiniteRelationPolynomial D d a s n)).vars at hz
  obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ hz
  have hn := i.isLt
  have hval := congrArg Prod.snd he
  change i.val = z.2 at hval
  omega

/-- 実際の反復関係式の有限初期多項式表示は一意。 -/
theorem deltaDivisionFiniteRelationPolynomial_unique
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ)
    (f : MvPolynomial (σ × Fin (n + 1)) A)
    (hf : relativeFreeFiniteInitialPolynomialMap (n + 1) σ A f =
      deltaDivisionIteratedRelation D d a s n) :
    f = deltaDivisionFiniteRelationPolynomial D d a s n :=
  relativeFreeFiniteInitialPolynomialMap_injective (n + 1) σ
    (hf.trans (deltaDivisionFiniteRelationPolynomial_image D d a s n).symm)

end SerrePositivity.BhattScholze
