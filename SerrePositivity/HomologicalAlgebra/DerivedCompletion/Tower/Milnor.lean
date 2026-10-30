module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Maps
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerProjection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # Milnor 列と一様に零な塔

## 概要

実際の holim のホモロジーについて、差分の余核（lim¹）→ ホモロジー → 差分の核（lim）の Milnor 短完全列を作り、任意の塔の射についての自然性を示す。Hⁱ で消える塔の射と Hⁱ⁻¹ で消える塔の射の合成は holim の Hⁱ で零になる。合成が一様に零な塔は lim も lim¹ も消え、ホモロジーが一様に零な塔の holim は非輪状である。定数塔では標準射が擬同型である。

## 方針

Milnor 列は差分の錐の長完全列から切り出す。一様零の場合は、差分写像がシフトの冪で逆を持つことから全単射性を示す。

## 規約

lim¹ の消滅は一般には仮定しない。MilnorAnnihilator は BS が import するので別ファイルのまま。

## 使われ方

導来完備化の H⁰ と零化、BS の Milnor 列による零化。
-/

@[expose] public noncomputable section

universe u v

section MilnorSequencePart

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

end MilnorSequencePart

section TowerHomologyNaturalityPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

lemma complexTowerHomologyShiftEquiv_naturality (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyShiftEquiv R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
        HomologicalComplex.homologyMap
          ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg))
          (i - 1) (complexTowerHomologyShiftEquiv R K t i x) := by
  exact congrArg (fun f => f.hom x)
    ((CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-1) i (i - 1)
      (by omega)).hom.naturality
        ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg)))

lemma complexTowerProjection_naturality :
    complexTowerHomotopyLimitMap R t s g hg ≫ complexTowerProjection R L s =
      complexTowerProjection R K t ≫ complexTowerProductMap R g := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [complexTowerHomotopyLimitMap, complexTowerProjection,
    CochainComplex.mappingCocone.fst, CochainComplex.HomComplex.Cochain.leftShift,
    CochainComplex.shiftFunctorObjXIso, cochainMappingConeFunctor,
    complexTowerDifferenceArrowMap]
  exact moduleConeArrowMap_fst
    (complexTowerDifference R K t) (complexTowerDifference R L s)
    (complexTowerDifferenceArrowMap R t s g hg) (n + -1) n (by change n + -1 + 1 = n; omega)

lemma complexTowerHomologyIncoming_naturality (i : ℤ)
    (y : ∀ n, (K n).homology (i - 1)) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i
      (complexTowerHomologyIncoming R K t i y) =
        complexTowerHomologyIncoming R L s i
          (fun n => HomologicalComplex.homologyMap (g n) (i - 1) (y n)) := by
  apply (complexTowerHomologyShiftEquiv R L s i).injective
  rw [complexTowerHomologyShiftEquiv_naturality]
  simp only [complexTowerHomologyIncoming, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  have h : CochainComplex.mappingCone.inr (complexTowerDifference R K t) ≫
      (cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg) =
        complexTowerProductMap R g ≫
          CochainComplex.mappingCone.inr (complexTowerDifference R L s) := by
    apply HomologicalComplex.hom_ext
    intro n
    exact cochainConeArrowMap_inr _ _ _ n
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f (i - 1)) h
  simp only [HomologicalComplex.homologyMap_comp] at hh
  change (HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr (complexTowerDifference R K t)) (i - 1) ≫
      HomologicalComplex.homologyMap
        ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg))
        (i - 1)) ((complexProductHomologyEquiv R K (i - 1)).symm y) = _
  rw [hh]
  change HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr (complexTowerDifference R L s)) (i - 1)
      (HomologicalComplex.homologyMap (complexTowerProductMap R g) (i - 1)
        ((complexProductHomologyEquiv R K (i - 1)).symm y)) = _
  congr 1
  apply (complexProductHomologyEquiv R L (i - 1)).injective
  ext n
  rw [complexTowerProductMap_homology]
  simp only [LinearEquiv.apply_symm_apply]

lemma complexTowerHomologyBoundary_naturality (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyBoundary R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
        fun n => HomologicalComplex.homologyMap (g n) i
          (complexTowerHomologyBoundary R K t i x n) := by
  rw [complexTowerHomologyBoundary_eq_neg_projection,
    complexTowerHomologyBoundary_eq_neg_projection]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (complexTowerProjection_naturality R t s g hg)
  simp only [HomologicalComplex.homologyMap_comp] at h
  ext n
  change -complexProductHomologyEquiv R L i
    (HomologicalComplex.homologyMap (complexTowerProjection R L s) i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x)) n = _
  have hx := congrArg (fun f => f.hom x) h
  change HomologicalComplex.homologyMap (complexTowerProjection R L s) i
    (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
      HomologicalComplex.homologyMap (complexTowerProductMap R g) i
        (HomologicalComplex.homologyMap (complexTowerProjection R K t) i x) at hx
  rw [hx, complexTowerProductMap_homology]
  simp only [Pi.neg_apply, map_neg]

end SerrePositivity.DerivedCompletion

end TowerHomologyNaturalityPart

section MilnorNaturalityPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

/-- The componentwise map on the original homology products. -/
def complexTowerHomologyProductMap (i : ℤ) :
    (∀ n, (K n).homology i) →ₗ[R] ∀ n, (L n).homology i :=
  LinearMap.pi (fun n => (HomologicalComplex.homologyMap (g n) i).hom.comp (LinearMap.proj n))

@[simp] lemma complexTowerHomologyProductMap_apply (i : ℤ)
    (y : ∀ n, (K n).homology i) (n : ℕ) :
    complexTowerHomologyProductMap R g i y n = HomologicalComplex.homologyMap (g n) i (y n) := rfl

include hg in
lemma complexTowerHomologyDifference_naturality (i : ℤ) (y : ∀ n, (K n).homology i) :
    complexTowerHomologyProductMap R g i (complexTowerHomologyDifference R K t i y) =
      complexTowerHomologyDifference R L s i (complexTowerHomologyProductMap R g i y) := by
  ext n
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i) (hg n)
  simp only [HomologicalComplex.homologyMap_comp] at h
  have hx := congrArg (fun f => f.hom (y (n + 1))) h
  simpa only [complexTowerHomologyProductMap_apply, complexTowerHomologyDifference,
    moduleTowerDifference_apply, map_sub, ModuleCat.comp_apply] using congrArg (fun z =>
      HomologicalComplex.homologyMap (g n) i (y n) - z) hx

/-- The original difference cokernels, with the induced map rather than a new lim¹. -/
def complexTowerHomologyLimOneMap (i : ℤ) :
    complexTowerHomologyLimOne R K t i →ₗ[R] complexTowerHomologyLimOne R L s i :=
  (complexTowerHomologyDifference R K t i).range.mapQ
    (complexTowerHomologyDifference R L s i).range (complexTowerHomologyProductMap R g i)
    (by
      rintro y ⟨z, rfl⟩
      exact ⟨complexTowerHomologyProductMap R g i z,
        (complexTowerHomologyDifference_naturality R t s g hg i z).symm⟩)

/-- The induced map on the original compatible homology sequences. -/
def complexTowerHomologyLimitMap (i : ℤ) :
    moduleTowerLimit R (fun n => (K n).homology i)
      (fun n => (HomologicalComplex.homologyMap (t n) i).hom) →ₗ[R]
    moduleTowerLimit R (fun n => (L n).homology i)
      (fun n => (HomologicalComplex.homologyMap (s n) i).hom) :=
  ((complexTowerHomologyProductMap R g i).comp
    (moduleTowerLimit R (fun n => (K n).homology i)
      (fun n => (HomologicalComplex.homologyMap (t n) i).hom)).subtype).codRestrict _ (by
        intro x
        change complexTowerHomologyDifference R L s i
          (complexTowerHomologyProductMap R g i x.val) = 0
        rw [← complexTowerHomologyDifference_naturality R t s g hg]
        have hx : complexTowerHomologyDifference R K t i x.val = 0 := x.property
        rw [hx, map_zero])

lemma complexTowerMilnorInclusion_naturality (i : ℤ)
    (y : complexTowerHomologyLimOne R K t (i - 1)) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i
      (complexTowerMilnorInclusion R K t i y) =
        complexTowerMilnorInclusion R L s i (complexTowerHomologyLimOneMap R t s g hg (i - 1) y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ y => exact complexTowerHomologyIncoming_naturality R t s g hg i y

lemma complexTowerMilnorProjection_naturality (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerMilnorProjection R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
        complexTowerHomologyLimitMap R t s g hg i (complexTowerMilnorProjection R K t i x) := by
  apply Subtype.ext
  exact complexTowerHomologyBoundary_naturality R t s g hg i x

/-- A genuine morphism of the existing Milnor short complexes. -/
def complexTowerMilnorSequenceMap (i : ℤ) :
    complexTowerMilnorSequence R K t i ⟶ complexTowerMilnorSequence R L s i :=
  { τ₁ := ModuleCat.ofHom (complexTowerHomologyLimOneMap R t s g hg (i - 1))
    τ₂ := HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i
    τ₃ := ModuleCat.ofHom (complexTowerHomologyLimitMap R t s g hg i)
    comm₁₂ := by ext y; exact (complexTowerMilnorInclusion_naturality R t s g hg i y).symm
    comm₂₃ := by ext x; exact complexTowerMilnorProjection_naturality R t s g hg i x }

end SerrePositivity.DerivedCompletion

end MilnorNaturalityPart

section MilnorMapZeroPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

lemma complexTowerHomologyLimitMap_eq_zero (i : ℤ)
    (h : ∀ n, HomologicalComplex.homologyMap (g n) i = 0) :
    complexTowerHomologyLimitMap R t s g hg i = 0 := by
  ext x n
  change HomologicalComplex.homologyMap (g n) i (x.val n) = 0
  rw [h n]
  rfl

lemma complexTowerHomologyLimOneMap_eq_zero (i : ℤ)
    (h : ∀ n, HomologicalComplex.homologyMap (g n) i = 0) :
    complexTowerHomologyLimOneMap R t s g hg i = 0 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change Submodule.Quotient.mk (complexTowerHomologyProductMap R g i y) = 0
    have hy : complexTowerHomologyProductMap R g i y = 0 := by
      ext n
      change HomologicalComplex.homologyMap (g n) i (y n) = 0
      rw [h n]
      rfl
    rw [hy]
    rfl

/-- Two maps killing the adjacent stage degrees have zero composite on holim Hⁱ. -/
lemma complexTowerHomotopyLimitMap_homology_comp_eq_zero
    {V : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (v : ∀ n, V (n + 1) ⟶ V n) (h : ∀ n, L n ⟶ V n)
    (hh : ∀ n, s n ≫ h n = h (n + 1) ≫ v n) (i : ℤ)
    (hg₀ : ∀ n, HomologicalComplex.homologyMap (g n) i = 0)
    (hh₀ : ∀ n, HomologicalComplex.homologyMap (h n) (i - 1) = 0) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i ≫
      HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R s v h hh) i = 0 := by
  ext x
  have hx : complexTowerMilnorProjection R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) = 0 := by
    rw [complexTowerMilnorProjection_naturality,
      complexTowerHomologyLimitMap_eq_zero R t s g hg i hg₀]
    rfl
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (complexTowerMilnorSequence_shortExact R L s i).exact _ hx
  change HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R s v h hh) i
    (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) = 0
  change complexTowerMilnorInclusion R L s i y = _ at hy
  rw [← hy, complexTowerMilnorInclusion_naturality,
    complexTowerHomologyLimOneMap_eq_zero R s v h hh (i - 1) hh₀]
  exact map_zero _

end SerrePositivity.DerivedCompletion

end MilnorMapZeroPart

section UniformZeroTowerPart

namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (M : ℕ → Type v)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n, M (n + 1) →ₗ[R] M n)

/-- The actual composite of `k` adjacent transition maps. -/
def moduleTowerComposite (n : ℕ) : ∀ k : ℕ, M (n + k) →ₗ[R] M n
  | 0 => LinearMap.id
  | k + 1 => (moduleTowerComposite n k).comp (t (n + k))

/-- Shift along the tower on the full product. -/
def moduleTowerShift : Module.End R (∀ n, M n) where
  toFun x n := t n (x (n + 1))
  map_add' x y := by ext n; exact map_add _ _ _
  map_smul' r x := by ext n; exact map_smul _ _ _

theorem moduleTowerShift_pow_apply (k : ℕ) (x : ∀ n, M n) (n : ℕ) :
    (moduleTowerShift R M t ^ k) x n = moduleTowerComposite R M t n k (x (n + k)) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    change (moduleTowerShift R M t ^ k) (moduleTowerShift R M t x) n = _
    rw [ih]
    rfl

/-- `1-shift` is a unit when all composites of one fixed length vanish. -/
theorem moduleTowerDifference_bijective_of_uniform_zero (N : ℕ)
    (h : ∀ n, moduleTowerComposite R M t n N = 0) :
    Function.Bijective (moduleTowerDifference R M t) := by
  have hn : IsNilpotent (moduleTowerShift R M t) := by
    refine ⟨N, ?_⟩
    ext x n
    rw [moduleTowerShift_pow_apply, h]
    rfl
  have he : moduleTowerDifference R M t = 1 - moduleTowerShift R M t := rfl
  rw [he]
  exact (Module.End.isUnit_iff _).mp hn.isUnit_one_sub

/-- The limit is zero without any surjectivity assumption on the transitions. -/
theorem moduleTowerLimit_subsingleton_of_uniform_zero (N : ℕ)
    (h : ∀ n, moduleTowerComposite R M t n N = 0) :
    Subsingleton (moduleTowerLimit R M t) := by
  have hi := (moduleTowerDifference_bijective_of_uniform_zero R M t N h).1
  refine ⟨fun x y ↦ Subtype.ext (hi (x.property.trans y.property.symm))⟩

end SerrePositivity.DerivedCompletion

end UniformZeroTowerPart

section UniformZeroTowerHomologyPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- The actual composite in the category of complexes. -/
def complexTowerComposite (n : ℕ) : ∀ k : ℕ, K (n + k) ⟶ K n
  | 0 => 𝟙 _
  | k + 1 => t (n + k) ≫ complexTowerComposite n k

/-- Taking homology preserves the full transition composite. -/
theorem complexTowerComposite_homology (n k : ℕ) (i : ℤ) :
    moduleTowerComposite R (fun n ↦ (K n).homology i)
      (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) n k =
        (HomologicalComplex.homologyMap (complexTowerComposite R K t n k) i).hom := by
  induction k with
  | zero => simp [moduleTowerComposite, complexTowerComposite]
  | succ k ih =>
    simp only [moduleTowerComposite, complexTowerComposite,
      HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, ih]

/-- A uniform zero composite in two adjacent homology towers kills holim homology.
The two lengths can differ, and no stage is assumed acyclic. -/
theorem complexTowerHolim_homology_isZero_of_uniform_zero (i : ℤ)
    (N₀ N₁ : ℕ)
    (h₀ : ∀ n, moduleTowerComposite R (fun n ↦ (K n).homology (i - 1))
      (fun n ↦ (HomologicalComplex.homologyMap (t n) (i - 1)).hom) n N₀ = 0)
    (h₁ : ∀ n, moduleTowerComposite R (fun n ↦ (K n).homology i)
      (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) n N₁ = 0) :
    IsZero ((complexTowerHomotopyLimit R K t).homology i) := by
  have hs := (moduleTowerDifference_bijective_of_uniform_zero R
    (fun n ↦ (K n).homology (i - 1))
    (fun n ↦ (HomologicalComplex.homologyMap (t n) (i - 1)).hom) N₀ h₀).2
  have hi := complexTowerMilnorProjection_injective_of_surjective R K t i hs
  have := moduleTowerLimit_subsingleton_of_uniform_zero R
    (fun n ↦ (K n).homology i)
    (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) N₁ h₁
  exact ModuleCat.isZero_iff_subsingleton.mpr hi.subsingleton

/-- A uniform zero composite of chain maps makes the actual holim acyclic. -/
theorem complexTowerHolim_acyclic_of_uniform_zero (N : ℕ)
    (h : ∀ n, complexTowerComposite R K t n N = 0) :
    (complexTowerHomotopyLimit R K t).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply complexTowerHolim_homology_isZero_of_uniform_zero R K t i N N
  all_goals
    intro n
    rw [complexTowerComposite_homology, h]
    simp

end SerrePositivity.DerivedCompletion

end UniformZeroTowerHomologyPart

section ConstantTowerPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 同一の複体を各段に置く定数塔。 -/
abbrev constantComplexTower (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ℕ → CochainComplex (ModuleCat.{u} R) ℤ := fun _ ↦ K

/-- 恒等遷移の定数塔への標準の対角射。 -/
def constantComplexTowerUnit (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ complexTowerHomotopyLimit R (constantComplexTower R K) (fun _ ↦ 𝟙 K) :=
  complexTowerCompatibleLift R _ _ K (fun _ ↦ 𝟙 K) (by intro n; simp)

/-- 対角射は全ての段への射影に対して恒等となる。 -/
theorem constantComplexTowerUnit_comp_projection (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℕ) :
    constantComplexTowerUnit R K ≫
      complexTowerProjection R (constantComplexTower R K) (fun _ ↦ 𝟙 K) ≫
        Pi.π (constantComplexTower R K) n = 𝟙 K := by
  rw [← Category.assoc, constantComplexTowerUnit,
    complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

/-- 恒等遷移の定数塔では、ホモロジー上の差分は全射。 -/
theorem constantComplexTowerHomologyDifference_surjective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Function.Surjective
      (complexTowerHomologyDifference R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i) := by
  apply moduleTowerDifference_surjective
  intro n y
  refine ⟨y, ?_⟩
  simp only [homologyMap_id, ModuleCat.hom_id, LinearMap.id_apply]

/-- Milnor列の符号規約では、対角射の境界像は定数列-xとなる。 -/
theorem constantComplexTowerUnit_boundary (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : ℤ) (x : K.homology i) (n : ℕ) :
    complexTowerHomologyBoundary R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i
      (homologyMap (constantComplexTowerUnit R K) i x) n = -x := by
  rw [complexTowerHomologyBoundary_eq_neg_projection]
  simp only [Pi.neg_apply, complexProductHomologyEquiv_apply]
  have h := congrArg (fun f ↦ homologyMap f i)
    (constantComplexTowerUnit_comp_projection R K n)
  simpa only [homologyMap_comp, homologyMap_id, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using
    congrArg (fun f ↦ -(f.hom x)) h

/-- 対角射は全次数のホモロジーで全単射。 -/
theorem constantComplexTowerUnit_homology_bijective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Function.Bijective (homologyMap (constantComplexTowerUnit R K) i) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z ↦ complexTowerHomologyBoundary R
      (constantComplexTower R K) (fun _ ↦ 𝟙 K) i z 0) h
    simpa only [constantComplexTowerUnit_boundary, neg_inj] using h'
  · intro y
    let z := complexTowerMilnorProjection R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i y
    have hz (n : ℕ) : z.val n = z.val 0 := by
      induction n with
      | zero => rfl
      | succ n ih =>
        have h := (mem_moduleTowerLimit_iff R _ _ z.val).mp z.property n
        simpa only [homologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] using h.trans ih
    refine ⟨-(z.val 0), ?_⟩
    apply complexTowerMilnorProjection_injective_of_surjective R
      (constantComplexTower R K) (fun _ ↦ 𝟙 K) i
      (constantComplexTowerHomologyDifference_surjective R K (i - 1))
    apply Subtype.ext
    funext n
    change complexTowerHomologyBoundary R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i
      (homologyMap (constantComplexTowerUnit R K) i (-(z.val 0))) n = z.val n
    rw [constantComplexTowerUnit_boundary, neg_neg]
    exact (hz n).symm

/-- 任意複体から恒等遷移の定数塔のholimへの標準射は準同型同値。 -/
theorem constantComplexTowerUnit_quasiIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso (constantComplexTowerUnit R K) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact constantComplexTowerUnit_homology_bijective R K i

end SerrePositivity.DerivedCompletion

end ConstantTowerPart
