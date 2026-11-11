module

public import SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarLocalizationRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedScalarRestriction

/-!
概要：斉次局所化の係数環比較を、加群写像に自然な形にする。
方針：斉次分数を代表に取り、両辺の分子が同じ写像の値になることを示す。
規約：局所化の係数環の変更と、加群の係数制限を区別する。
使われ方：Rees の標準開比較で、斉次係数の作用を追う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

section Change
variable {R P Q M N : Type*} [CommRing R] [CommRing P] [CommRing Q]
variable [Algebra R P] [Algebra P Q] [Algebra R Q] [IsScalarTower R P Q]
variable [AddCommGroup M] [Module R M] [Module P M] [Module Q M]
variable [IsScalarTower R P M] [IsScalarTower R Q M] [IsScalarTower P Q M]
variable [AddCommGroup N] [Module R N] [Module P N] [Module Q N]
variable [IsScalarTower R P N] [IsScalarTower R Q N] [IsScalarTower P Q N]

/-- 分母の同定を含む係数環比較は、分子の次数を保つ加群写像に自然。 -/
theorem projectiveModuleScalarGradedAwayLinearEquivOfEq_map
    (f : P) (g : Q) (hg : algebraMap P Q f = g)
    (V : ℕ → Submodule R M) (W : ℕ → Submodule R N)
    (u : M →ₗ[Q] N) (hu : ∀ n, ∀ m ∈ V n, u m ∈ W n)
    (hstep : ∀ n (m : V n), f • m.val ∈ V (n + 1))
    (z : projectiveGradedAway f V) :
    projectiveModuleScalarGradedAwayLinearEquivOfEq (R := R) f g hg W
        (projectiveGradedAwayMap f V W (u.restrictScalars P) hu z) =
      projectiveGradedAwayMap g V W u hu
        (projectiveModuleScalarGradedAwayLinearEquivOfEq (R := R) f g hg V z) := by
  obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f V hstep z.val).mp z.property
  have hp := projectiveGradedAwayMap_fraction f V W (u.restrictScalars P) hu n m z hm
  have he := projectiveModuleScalarGradedAwayLinearEquivOfEq_fraction
    (R := R) f g hg V n m z hm
  apply Subtype.ext
  rw [projectiveModuleScalarGradedAwayLinearEquivOfEq_fraction
    (R := R) f g hg W n ⟨u m.val, hu n m.val m.property⟩ _ hp.symm]
  rw [projectiveGradedAwayMap_fraction g V W u hu n m _ he.symm]

end Change

section Restriction
variable {R B Q M N : Type*} [CommRing R] [CommRing B] [CommRing Q]
variable [Algebra R B] [Algebra B Q] [Algebra R Q] [IsScalarTower R B Q]
variable [AddCommGroup M] [Module R M] [Module B M] [Module Q M]
variable [IsScalarTower R B M] [IsScalarTower R Q M] [IsScalarTower B Q M]
variable [AddCommGroup N] [Module R N] [Module B N] [Module Q N]
variable [IsScalarTower R B N] [IsScalarTower R Q N] [IsScalarTower B Q N]

/-- 斉次局所化の係数制限の比較は、分子の次数を保つ加群写像に自然。 -/
theorem projectiveGradedAwayScalarRestrictionLinearEquiv_map
    (f : Q) (V : ℕ → Submodule B M) (W : ℕ → Submodule B N)
    (u : M →ₗ[Q] N) (hu : ∀ n, ∀ m ∈ V n, u m ∈ W n)
    (z : projectiveGradedAway f (fun n ↦ (V n).restrictScalars R)) :
    projectiveGradedAwayScalarRestrictionLinearEquiv (R := R) f W
        (projectiveGradedAwayMap f (fun n ↦ (V n).restrictScalars R)
          (fun n ↦ (W n).restrictScalars R) u hu z) =
      projectiveGradedAwayMap (R := B) f V W u hu
        (projectiveGradedAwayScalarRestrictionLinearEquiv (R := R) f V z) := by
  apply Subtype.ext
  rfl

end Restriction
end SerrePositivity.AlgebraicGeometry
