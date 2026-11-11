module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization
public import Mathlib.Algebra.Group.Commute.Units

/-!
概要：標準開を狭めるとき、局所化加群の指定次数成分を制限する。
方針：分母を広げる元の冪を分子にも掛ける。
規約：元の分母が f、新しい分母が f * g と書けるとする。
使われ方：次数付き加群から標準開 Čech の係数図式を作る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- f が g を割ると、g で局所化した加群では f の作用も可逆になる。 -/
theorem isUnit_projectiveModuleAwayFactor {f g : S} (h : f ∣ g) (s : Submonoid.powers f) :
    IsUnit (algebraMap S (Module.End S (LocalizedModule (Submonoid.powers g) M)) s.val) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨_, n, rfl⟩ := s
  let A := Module.End S (LocalizedModule (Submonoid.powers g) M)
  have hunit : IsUnit (algebraMap S A g) := by
    have h := IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (projDenominator g 1)
    simpa [projDenominator] using h
  have hfactor : IsUnit (algebraMap S A f * algebraMap S A a) := by
    rw [← map_mul, ← ha]
    exact hunit
  have hc : Commute (algebraMap S A f) (algebraMap S A a) :=
    (Commute.all f a).map (algebraMap S A)
  change IsUnit (algebraMap S A (f ^ n))
  rw [map_pow]
  exact ((hc.isUnit_mul_iff.mp hfactor).1).pow n

/-- 分母の整除関係が誘導する局所化加群の制限。 -/
def projectiveModuleAwayRestriction {f g : S} (h : f ∣ g) :
    LocalizedModule (Submonoid.powers f) M →ₗ[S]
      LocalizedModule (Submonoid.powers g) M :=
  LocalizedModule.lift (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (isUnit_projectiveModuleAwayFactor h)

@[simp]
theorem projectiveModuleAwayRestriction_mk_one {f g : S} (h : f ∣ g) (m : M) :
    projectiveModuleAwayRestriction h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  simp [projectiveModuleAwayRestriction]

/-- 制限写像の合成は、分母の整除関係の推移から得る制限写像。 -/
theorem projectiveModuleAwayRestriction_comp {f g k : S} (h : f ∣ g) (h' : g ∣ k) :
    (projectiveModuleAwayRestriction (M := M) h').comp (projectiveModuleAwayRestriction h) =
      projectiveModuleAwayRestriction (h.trans h') := by
  symm
  apply LocalizedModule.lift_unique
  ext m
  simp [LocalizedModule.mkLinearMap_apply]

/-- 同じ分母での制限写像は恒等。 -/
theorem projectiveModuleAwayRestriction_refl (f : S) :
    projectiveModuleAwayRestriction (M := M) (dvd_refl f) = LinearMap.id := by
  apply LocalizedModule.lift_unique
  ext m
  rfl

/-- 制限は分子に追加因子の冪を掛け、分母を新しい分母の冪へ移す。 -/
theorem projectiveModuleAwayRestriction_mk {f g a : S} (ha : g = f * a)
    (n : ℕ) (m : M) :
    projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (LocalizedModule.mk m (projDenominator f n)) =
      LocalizedModule.mk (a ^ n • m) (projDenominator g n) := by
  unfold projectiveModuleAwayRestriction
  rw [LocalizedModule.lift_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff,
    LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk]
  change LocalizedModule.mk m 1 =
    LocalizedModule.mk (f ^ n • a ^ n • m) (projDenominator g n)
  rw [← mul_smul, ← mul_pow, ← ha]
  exact (LocalizedModule.mk_cancel (projDenominator g n) m).symm

/-- 分子の指定次数を保つとき、制限は局所化の指定次数成分にも降りる。 -/
def projectiveGradedAwayRestriction {f g a : S} (ha : g = f * a)
    (V W : ℕ → Submodule R M) (h : ∀ (n : ℕ) (m : V n), a ^ n • m.val ∈ W n) :
    projectiveGradedAway f V →ₗ[R] projectiveGradedAway g W := by
  let F := (projectiveModuleAwayRestriction (M := M) (show f ∣ g from ⟨a, ha⟩)).restrictScalars R
  have hle : projectiveGradedAway f V ≤ (projectiveGradedAway g W).comap F := by
    apply iSup_le
    intro n y hy
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hy
    change F (projectiveGradedFraction f V n m) ∈ projectiveGradedAway g W
    apply (le_iSup (fun n ↦ LinearMap.range (projectiveGradedFraction g W n)) n)
    refine LinearMap.mem_range.mpr ⟨⟨a ^ n • m.val, h n m⟩, ?_⟩
    simp only [projectiveGradedFraction_apply]
    exact (projectiveModuleAwayRestriction_mk ha n m.val).symm
  exact LinearMap.codRestrict _ (F.comp (projectiveGradedAway f V).subtype) (fun y ↦ hle y.property)

/-- 次数成分の制限は通常の局所化加群の制限で与えられる。 -/
@[simp]
theorem projectiveGradedAwayRestriction_val {f g a : S} (ha : g = f * a)
    (V W : ℕ → Submodule R M) (h : ∀ (n : ℕ) (m : V n), a ^ n • m.val ∈ W n)
    (z : projectiveGradedAway f V) :
    (projectiveGradedAwayRestriction ha V W h z).val =
      projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) z.val := rfl

end SerrePositivity.AlgebraicGeometry
