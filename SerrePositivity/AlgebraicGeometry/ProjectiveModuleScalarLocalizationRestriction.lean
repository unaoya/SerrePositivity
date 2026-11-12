module

public import SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarGradedLocalization
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction

/-!
概要：局所化する係数環の変更と、標準開を狭める制限との可換性。
方針：分母の冪の像をそろえ、追加因子の冪による分子の作用を比較する。
規約：同じ加群の二つの係数環による局所化を比較し、テンソル積の底変換とは区別する。
使われ方：Rees 加群の P 上と B[X] 上の標準開の比較を図式にまとめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

variable {R P Q M : Type*} [CommRing R] [CommRing P] [CommRing Q]
variable [Algebra R P] [Algebra P Q] [Algebra R Q] [IsScalarTower R P Q]
variable [AddCommGroup M] [Module R M] [Module P M] [Module Q M]
variable [IsScalarTower R P M] [IsScalarTower R Q M] [IsScalarTower P Q M]

/-- 係数環の変更は、斉次分数で使う分母の冪をその像の同じ冪へ写す。 -/
theorem projectiveModuleScalarLocalizationLinearEquiv_mk_pow (f : P) (k : ℕ) (m : M) :
    projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) f
        (LocalizedModule.mk m (projDenominator f k)) =
      LocalizedModule.mk m (projDenominator (algebraMap P Q f) k) := by
  rw [projectiveModuleScalarLocalizationLinearEquiv_mk]
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap P Q) f k

/-- 係数環の変更は、分母を広げる局所化の制限と可換。 -/
theorem projectiveModuleScalarLocalizationLinearEquiv_restriction
    {f g a : P} (ha : g = f * a) (z : LocalizedModule (Submonoid.powers f) M) :
    projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) g
        (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) z) =
      projectiveModuleAwayRestriction
        (show algebraMap P Q f ∣ algebraMap P Q g from
          ⟨algebraMap P Q a, by rw [ha, map_mul]⟩)
        (projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) f z) := by
  have haQ : algebraMap P Q g = algebraMap P Q f * algebraMap P Q a := by rw [ha, map_mul]
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨s, k, rfl⟩ := s
    change projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) g
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (LocalizedModule.mk m (projDenominator f k))) =
      projectiveModuleAwayRestriction
        (show algebraMap P Q f ∣ algebraMap P Q g from ⟨algebraMap P Q a, haQ⟩)
        (projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) f
          (LocalizedModule.mk m (projDenominator f k)))
    rw [projectiveModuleAwayRestriction_mk ha,
      projectiveModuleScalarLocalizationLinearEquiv_mk_pow,
      projectiveModuleScalarLocalizationLinearEquiv_mk_pow,
      projectiveModuleAwayRestriction_mk haQ, ← map_pow, algebraMap_smul Q]

/-- 分子を追加因子で移す条件は、係数環へ写した追加因子でも成り立つ。 -/
theorem projectiveModuleScalarGradedRestriction_mem (a : P)
    (V W : ℕ → Submodule R M)
    (h : ∀ k (m : V k), a ^ k • m.val ∈ W k) (k : ℕ) (m : V k) :
    (algebraMap P Q a) ^ k • m.val ∈ W k := by
  rw [← map_pow, algebraMap_smul Q]
  exact h k m

/-- 斉次成分での係数環の変更も、標準開の制限に自然。 -/
theorem projectiveModuleScalarGradedAwayLinearEquiv_restriction
    {f g a : P} (ha : g = f * a) (V W : ℕ → Submodule R M)
    (hP : ∀ k (m : V k), a ^ k • m.val ∈ W k)
    (hQ : ∀ k (m : V k), (algebraMap P Q a) ^ k • m.val ∈ W k)
    (z : projectiveGradedAway f V) :
    projectiveModuleScalarGradedAwayLinearEquiv (R := R) (Q := Q) g W
        (projectiveGradedAwayRestriction ha V W hP z) =
      projectiveGradedAwayRestriction (show algebraMap P Q g =
          algebraMap P Q f * algebraMap P Q a from by rw [ha, map_mul]) V W hQ
        (projectiveModuleScalarGradedAwayLinearEquiv (R := R) (Q := Q) f V z) := by
  apply Subtype.ext
  rw [projectiveModuleScalarGradedAwayLinearEquiv_val, projectiveGradedAwayRestriction_val,
    projectiveGradedAwayRestriction_val, projectiveModuleScalarGradedAwayLinearEquiv_val]
  exact projectiveModuleScalarLocalizationLinearEquiv_restriction (R := R) (Q := Q) ha z.val

/-- 分母の像を別の指定された分母と同定して、係数環の変更を行う。 -/
def projectiveModuleScalarGradedAwayLinearEquivOfEq (f : P) (g : Q)
    (hg : algebraMap P Q f = g) (V : ℕ → Submodule R M) :
    projectiveGradedAway f V ≃ₗ[R] projectiveGradedAway g V := by
  subst g
  exact projectiveModuleScalarGradedAwayLinearEquiv (R := R) (Q := Q) f V

/-- 指定した分母との同定を含む比較も、分子と分母の冪の表示を保つ。 -/
theorem projectiveModuleScalarGradedAwayLinearEquivOfEq_fraction (f : P) (g : Q)
    (hg : algebraMap P Q f = g) (V : ℕ → Submodule R M)
    (k : ℕ) (m : V k) (z : projectiveGradedAway f V)
    (hz : projectiveGradedFraction f V k m = z.val) :
    (projectiveModuleScalarGradedAwayLinearEquivOfEq (R := R) f g hg V z).val =
      projectiveGradedFraction g V k m := by
  subst g
  change (projectiveModuleScalarGradedAwayLinearEquiv (R := R) (Q := Q) f V z).val = _
  rw [projectiveModuleScalarGradedAwayLinearEquiv_val, ← hz,
    projectiveGradedFraction_apply, projectiveGradedFraction_apply,
    projectiveModuleScalarLocalizationLinearEquiv_mk_pow]

/-- 分母の像を標準分母と同定した係数環の変更は、標準開の制限にも自然。 -/
theorem projectiveModuleScalarGradedAwayLinearEquivOfEq_restriction
    {f g a : P} (ha : g = f * a) {f' g' a' : Q}
    (hf : algebraMap P Q f = f') (hg : algebraMap P Q g = g')
    (ha' : algebraMap P Q a = a') (hQ : g' = f' * a')
    (V W : ℕ → Submodule R M)
    (hPmem : ∀ k (m : V k), a ^ k • m.val ∈ W k)
    (hQmem : ∀ k (m : V k), a' ^ k • m.val ∈ W k)
    (z : projectiveGradedAway f V) :
    projectiveModuleScalarGradedAwayLinearEquivOfEq (R := R) g g' hg W
        (projectiveGradedAwayRestriction ha V W hPmem z) =
      projectiveGradedAwayRestriction hQ V W hQmem
        (projectiveModuleScalarGradedAwayLinearEquivOfEq (R := R) f f' hf V z) := by
  subst f'
  subst g'
  subst a'
  exact projectiveModuleScalarGradedAwayLinearEquiv_restriction
    (R := R) (Q := Q) ha V W hPmem hQmem z

end SerrePositivity.AlgebraicGeometry
