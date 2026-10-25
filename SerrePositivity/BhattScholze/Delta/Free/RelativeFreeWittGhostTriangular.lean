module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWittGhostSupport

/-! # 全Witt係数の最高δ変数係数1の有限三角形表示

下位変数所属から初期有限多項式を取り出し、表示の一意性も確認する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 全段でWitt係数は最高δ変数と、その手前の有限多項式の和。 -/
theorem exists_relativeFreeWittGhostLowerPolynomial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    ∃ c : MvPolynomial (σ × Fin n) A, relativeFreeWittGhostCoefficient D s n =
      MvPolynomial.X (s, n) + relativeFreeFiniteInitialPolynomialMap n σ A c := by
  let f := relativeFreeWittGhostCoefficient D s n - MvPolynomial.X (s, n)
  have hs := MvPolynomial.mem_supported.mp
    (relativeFreeWittGhostCoefficient_sub_X_mem_supported D hp s n)
  let ι : σ × Fin n → σ × ℕ := fun x => (x.1, x.2.val)
  have hi : Function.Injective ι := by
    intro x y h
    exact Prod.ext (congrArg (fun z : σ × ℕ => z.1) h)
      (Fin.ext (congrArg (fun z : σ × ℕ => z.2) h))
  have hv : (f.vars : Set (σ × ℕ)) ⊆ Set.range ι := by
    intro z hz
    have hz' : z.2 < n := hs hz
    exact ⟨(z.1, ⟨z.2, hz'⟩), rfl⟩
  obtain ⟨c, hc⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range f ι hi hv
  change relativeFreeFiniteInitialPolynomialMap n σ A c =
    relativeFreeWittGhostCoefficient D s n - MvPolynomial.X (s, n) at hc
  refine ⟨c, ?_⟩
  rw [hc]
  ring

/-- 全段の三角形表示で現れる初期n段の具体的な下位多項式。 -/
def relativeFreeWittGhostLowerPolynomial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    MvPolynomial (σ × Fin n) A :=
  Classical.choose (exists_relativeFreeWittGhostLowerPolynomial D hp s n)

/-- 構成した下位多項式による、最高δ変数係数1の全段の正確な表示。 -/
theorem relativeFreeWittGhostCoefficient_eq_X_add_lower (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittGhostCoefficient D s n = MvPolynomial.X (s, n) +
      relativeFreeFiniteInitialPolynomialMap n σ A
        (relativeFreeWittGhostLowerPolynomial D hp s n) :=
  Classical.choose_spec (exists_relativeFreeWittGhostLowerPolynomial D hp s n)

/-- この初期n段の下位多項式表示は一意。 -/
theorem relativeFreeWittGhostLowerPolynomial_unique (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ)
    (c : MvPolynomial (σ × Fin n) A)
    (hc : relativeFreeWittGhostCoefficient D s n =
      MvPolynomial.X (s, n) + relativeFreeFiniteInitialPolynomialMap n σ A c) :
    c = relativeFreeWittGhostLowerPolynomial D hp s n := by
  apply relativeFreeFiniteInitialPolynomialMap_injective n σ
  exact add_left_cancel (hc.symm.trans (relativeFreeWittGhostCoefficient_eq_X_add_lower D hp s n))

/-- 第0段の下位多項式は零。 -/
@[simp] theorem relativeFreeWittGhostLowerPolynomial_zero (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) :
    relativeFreeWittGhostLowerPolynomial D hp s 0 = 0 := by
  symm
  apply relativeFreeWittGhostLowerPolynomial_unique
  simp only [relativeFreeWittGhostCoefficient_zero, map_zero, add_zero]

end SerrePositivity.BhattScholze
