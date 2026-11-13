module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction

/-!
概要：分母を冪に送る局所化の半線形写像を、指定次数部分へ制限する。
方針：分数の表示から分子の所属を使い、対象の次数部分へ入ることを示す。
規約：周囲の局所化の写像と同じ値を持つ。
使われ方：閉厚化 Frobenius の標準開の係数図式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R P A B : Type u} [CommRing R] [CommRing P] [CommRing A] [CommRing B]
variable [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable [Algebra R B] [Algebra P B] [IsScalarTower R P B]
variable (ρ : R →+* R) (φ : A →+* B) (s : P) (k : ℕ)
variable (hd : φ (algebraMap P A s) = (algebraMap P B s) ^ k)
variable (hs : ∀ r, φ (algebraMap R A r) = algebraMap R B (ρ r))


variable (V : ℕ → Submodule R A) (W : ℕ → Submodule R B)
variable (hstep : ∀ n (x : V n), s • x.val ∈ V (n + 1))
variable (hpiece : ∀ n (x : V n), φ x.val ∈ W (k * n))

/-- 分子の次数条件から、指定次数の局所化の間の半線形写像を得る。 -/
def projectiveGradedAwayPowerMap : projectiveGradedAway s V →ₛₗ[ρ]
    projectiveGradedAway s W := by
  let F := projectiveLocalizedPowerMap ρ φ s k hd hs
  have hmem (z : projectiveGradedAway s V) : F z.val ∈ projectiveGradedAway s W := by
    obtain ⟨n, x, hx⟩ := (mem_projectiveGradedAway_iff s V hstep z.val).mp z.property
    apply (le_iSup (fun j ↦ LinearMap.range (projectiveGradedFraction s W j)) (k * n))
    refine ⟨⟨φ x.val, hpiece n x⟩, ?_⟩
    rw [← hx, projectiveGradedFraction_apply, projectiveGradedFraction_apply]
    exact (projectiveLocalizedPowerMap_fraction ρ φ s k hd hs x.val n).symm
  exact (F.domRestrict (projectiveGradedAway s V)).codRestrict _ hmem

/-- 指定次数部分の写像は、周囲の加群局所化の写像の制限。 -/
theorem projectiveGradedAwayPowerMap_val (z : projectiveGradedAway s V) :
    (projectiveGradedAwayPowerMap ρ φ s k hd hs V W hstep hpiece z).val =
      projectiveLocalizedPowerMap ρ φ s k hd hs z.val := rfl

end SerrePositivity.AlgebraicGeometry
