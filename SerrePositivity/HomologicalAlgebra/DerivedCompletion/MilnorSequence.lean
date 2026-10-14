module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerHomology

/-! # 可算逆系のホモロジーのMilnor短完全列

実際のmapping coneによるホモトピー逆極限に対し、
差分の余核 → ホモロジー → 差分の核を短完全列として構成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- 可算逆系のホモロジーのlim¹を、直積上の差分の余核で表す。 -/
abbrev complexTowerHomologyLimOne (i : ℤ) :=
  (∀ n, (K n).homology i) ⧸ (complexTowerHomologyDifference R K t i).range

/-- Milnor列の左の射。前の次数の差分の像を商にする。 -/
def complexTowerMilnorInclusion (i : ℤ) :
    complexTowerHomologyLimOne R K t (i - 1) →ₗ[R]
      (complexTowerHomotopyLimit R K t).homology i :=
  (complexTowerHomologyDifference R K t (i - 1)).range.liftQ
    (complexTowerHomologyIncoming R K t i) (by
      rintro y ⟨z, rfl⟩
      exact (complexTowerHomologyIncoming_zero_iff R K t i _).mpr ⟨z, rfl⟩)

@[simp] theorem complexTowerMilnorInclusion_mk (i : ℤ)
    (y : ∀ n, (K n).homology (i - 1)) :
    complexTowerMilnorInclusion R K t i (Submodule.Quotient.mk y) =
      complexTowerHomologyIncoming R K t i y := rfl

/-- Milnor列の右の射。連結射の像を両立するホモロジー列に制限する。 -/
def complexTowerMilnorProjection (i : ℤ) :
    (complexTowerHomotopyLimit R K t).homology i →ₗ[R]
      moduleTowerLimit R (fun n ↦ (K n).homology i)
        (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) :=
  (complexTowerHomologyBoundary R K t i).codRestrict _ (fun x ↦ by
    change complexTowerHomologyBoundary R K t i x ∈
      (complexTowerHomologyDifference R K t i).ker
    rw [← complexTowerHomologyBoundary_range R K t i]
    exact ⟨x, rfl⟩)

/-- Milnor列の左の射は単射。 -/
theorem complexTowerMilnorInclusion_injective (i : ℤ) :
    Function.Injective (complexTowerMilnorInclusion R K t i) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    intro hy
    rw [complexTowerMilnorInclusion_mk] at hy
    obtain ⟨z, hz⟩ := (complexTowerHomologyIncoming_zero_iff R K t i y).mp hy
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, hz⟩

/-- Milnor列の右の射は全射。 -/
theorem complexTowerMilnorProjection_surjective (i : ℤ) :
    Function.Surjective (complexTowerMilnorProjection R K t i) := by
  intro y
  have hy : y.val ∈ (complexTowerHomologyBoundary R K t i).range := by
    rw [complexTowerHomologyBoundary_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

/-- Milnor列の二つの射の合成は零。 -/
theorem complexTowerMilnor_comp (i : ℤ) :
    (complexTowerMilnorProjection R K t i).comp (complexTowerMilnorInclusion R K t i) = 0 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    apply Subtype.ext
    change complexTowerHomologyBoundary R K t i
      (complexTowerHomologyIncoming R K t i y) = 0
    exact (complexTowerHomologyBoundary_zero_iff R K t i _).mpr ⟨y, rfl⟩

/-- 可算逆系のホモロジーのMilnor短複体。 -/
def complexTowerMilnorSequence (i : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (complexTowerMilnorInclusion R K t i)
    (complexTowerMilnorProjection R K t i) (complexTowerMilnor_comp R K t i)

/-- 0 → lim¹ H^(i-1) → H^i(holim K) → lim H^i → 0 は短完全列。 -/
theorem complexTowerMilnorSequence_shortExact (i : ℤ) :
    (complexTowerMilnorSequence R K t i).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    have hx' : complexTowerHomologyBoundary R K t i x = 0 :=
      congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (complexTowerHomologyBoundary_zero_iff R K t i x).mp hx'
    exact ⟨Submodule.Quotient.mk y, hy⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (complexTowerMilnorInclusion_injective R K t i)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (complexTowerMilnorProjection_surjective R K t i)

/-- 前の次数の差分が全射なら、Milnor列の右の射は単射でもある。 -/
theorem complexTowerMilnorProjection_injective_of_surjective (i : ℤ)
    (h : Function.Surjective (complexTowerHomologyDifference R K t (i - 1))) :
    Function.Injective (complexTowerMilnorProjection R K t i) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hx' : complexTowerHomologyBoundary R K t i x = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := (complexTowerHomologyBoundary_zero_iff R K t i x).mp hx'
  obtain ⟨z, hz⟩ := h y
  exact hy.symm.trans ((complexTowerHomologyIncoming_zero_iff R K t i y).mpr ⟨z, hz⟩)

/-- lim¹の寄与が零になる明示的な条件の下でのホモロジーの同型。 -/
def complexTowerMilnorProjectionEquiv (i : ℤ)
    (h : Function.Surjective (complexTowerHomologyDifference R K t (i - 1))) :
    (complexTowerHomotopyLimit R K t).homology i ≃ₗ[R]
      moduleTowerLimit R (fun n ↦ (K n).homology i)
        (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) :=
  LinearEquiv.ofBijective (complexTowerMilnorProjection R K t i)
    ⟨complexTowerMilnorProjection_injective_of_surjective R K t i h,
      complexTowerMilnorProjection_surjective R K t i⟩

end SerrePositivity.DerivedCompletion
