module

public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquareClass
public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquare
public import SerrePositivity.PerfectComplex.Eigen.InvolutionTensor
public import SerrePositivity.PerfectComplex.KoszulClasses
public import SerrePositivity.KTheory.Adams.KoszulSquareSplitting
public import SerrePositivity.PerfectComplex.KoszulTensor
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.KTheory.Adams.Family

/-! # 次数 2 の巡回 Adams 作用素

## 概要

次数 2 の巡回 Adams 作用素（テンソル二乗の符号付き対称性の固有分解の差）を定め、その乗法性（カップ積との可換性 `cyclicTwo_cup`）、台の拡大・環の変更との自然性、単位の類と一元 Koszul 複体での正規化を示し、局所化の族の共通の契約を満たすこと（`cyclicTwoFamily`）を与える。

## 方針

乗法性はテンソル二乗の対称性のシャッフルとの両立から示す。

## 規約

2 が可逆な係数で使う。

## 使われ方

IntersectionMultiplicity/Vanishing（剰余標数 2 以外）。
-/

@[expose] public noncomputable section

universe u v

section CyclicTwoPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

/-- The cyclic Adams operation on the closed-support Grothendieck group. -/
def cyclicTwo : K0WithSupport Z →+ K0WithSupport Z :=
  K0WithSupport.lift Z (tensorSquareEvaluation Z)
    (tensorSquareEvaluation_iso Z) (tensorSquareEvaluation_triangle Z)

@[simp]
lemma cyclicTwo_mk (X : SupportedPerfectHomotopyOn Z) :
    cyclicTwo Z (K0WithSupport.mk Z X) = tensorSquareEvaluation Z X :=
  K0WithSupport.lift_mk Z (tensorSquareEvaluation Z)
    (tensorSquareEvaluation_iso Z) (tensorSquareEvaluation_triangle Z) X

lemma cyclicTwo_mk_concrete (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    cyclicTwo Z (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
      tensorSquareClass P Z hp hs := cyclicTwo_mk Z _

lemma cyclicTwo_unique (F : K0WithSupport Z →+ K0WithSupport Z)
    (h : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P),
      F (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) = tensorSquareClass P Z hp hs) :
    F = cyclicTwo Z := by
  apply K0WithSupport.hom_ext
  intro X
  rw [cyclicTwo_mk]
  exact h (supportedPerfectRepresentative X) (supportedPerfectRepresentative_perfect X)
    (supportedPerfectRepresentative_support X)

end Adams
end SerrePositivity

end CyclicTwoPart

section TensorSquareMultiplicativityPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace Adams

lemma tensorSquareClass_tensor (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    tensorSquareClass (cochainTensor P Q) (Y ⊓ Z)
      (strictlyPerfectComplex_cochainTensor P Q hp hq) (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (tensorSquareClass P Y hp hsP) (tensorSquareClass Q Z hq hsQ) := by
  let hT := strictlyPerfectComplex_cochainTensor P Q hp hq
  let sT := hsP.cochainTensor hsQ hp hq
  let hP := tensorSquare_perfect P hp
  let hQ := tensorSquare_perfect Q hq
  let sP := tensorSquare_support hp hsP
  let sQ := tensorSquare_support hq hsQ
  let t := (tensorSquareInvolution P).tensor (tensorSquareInvolution Q)
  have hpos := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (tensorSquarePositive (cochainTensor P Q)) t.positive.image
    (tensorSquarePositive_perfect _ hT)
    (t.positive.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor _ _ hP hQ))
    (tensorSquarePositive_support hT sT) (t.positive.image_support (sP.cochainTensor sQ hP hQ))
    (tensorSquareTensorPositiveIso P Q).hom
  have hneg := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (tensorSquareNegative (cochainTensor P Q)) t.negative.image
    (tensorSquareNegative_perfect _ hT)
    (t.negative.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor _ _ hP hQ))
    (tensorSquareNegative_support hT sT) (t.negative.image_support (sP.cochainTensor sQ hP hQ))
    (tensorSquareTensorNegativeIso P Q).hom
  have he := congrArg₂ (fun x y : K0WithSupport (Y ⊓ Z) => x - y) hpos hneg
  exact he.trans (CochainInvolution.k0Class_tensor (tensorSquareInvolution P)
    (tensorSquareInvolution Q) hP hQ sP sQ)

/-- Axiom A2 for arbitrary classes in closed-support K₀. -/
lemma cyclicTwo_cup {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (x : K0WithSupport Y) (y : K0WithSupport Z) :
    cyclicTwo (Y ⊓ Z) (K0WithSupport.cup x y) =
      K0WithSupport.cup (cyclicTwo Y x) (cyclicTwo Z y) := by
  have hx : ∀ (X : SupportedPerfectHomotopyOn Y) (y : K0WithSupport Z),
      cyclicTwo (Y ⊓ Z) (K0WithSupport.cup (K0WithSupport.mk Y X) y) =
      K0WithSupport.cup (cyclicTwo Y (K0WithSupport.mk Y X)) (cyclicTwo Z y) := by
    intro X
    have he : (cyclicTwo (Y ⊓ Z)).comp (K0WithSupport.cup (K0WithSupport.mk Y X)) =
        (K0WithSupport.cup (cyclicTwo Y (K0WithSupport.mk Y X))).comp (cyclicTwo Z) := by
      apply K0WithSupport.hom_ext
      intro Q
      change cyclicTwo (Y ⊓ Z) (K0WithSupport.cup (K0WithSupport.mk Y X) (K0WithSupport.mk Z Q)) =
        K0WithSupport.cup (cyclicTwo Y (K0WithSupport.mk Y X)) (cyclicTwo Z (K0WithSupport.mk Z Q))
      rw [K0WithSupport.cup_mk_mk]
      change cyclicTwo (Y ⊓ Z) (K0WithSupport.mk (Y ⊓ Z) (supportedPerfectTensorObj X Q)) = _
      rw [cyclicTwo_mk, cyclicTwo_mk, cyclicTwo_mk]
      exact tensorSquareClass_tensor (supportedPerfectRepresentative X)
        (supportedPerfectRepresentative Q)
        (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_perfect Q)
        (supportedPerfectRepresentative_support X) (supportedPerfectRepresentative_support Q)
    intro y
    exact DFunLike.congr_fun he y
  have he : (cyclicTwo (Y ⊓ Z)).comp (K0WithSupport.cup.flip y) =
      (K0WithSupport.cup.flip (cyclicTwo Z y)).comp (cyclicTwo Y) := by
    apply K0WithSupport.hom_ext
    intro X
    exact hx X y
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity

end TensorSquareMultiplicativityPart

section KoszulNormalizationPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

lemma oneKoszulShiftOne_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (oneKoszulShiftOne a) (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
      (oneKoszulNegativeModel_support a)) = -oneKoszulClass a :=
  oneKoszulClass_shift_one a

variable [Invertible (2 : R)]

lemma oneKoszulPositive_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (tensorSquarePositive (oneKoszulComplex a))
      (tensorSquarePositive_perfect _ (oneKoszulComplex_perfect a))
      (tensorSquarePositive_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))) =
    oneKoszulClass a := by
  have he := K0WithSupport.mk_eq_of_quasiIso (oneKoszulSupport a)
    (tensorSquarePositive (oneKoszulComplex a)) (oneKoszulComplex (2 * a))
    (tensorSquarePositive_perfect _ (oneKoszulComplex_perfect a)) (oneKoszulComplex_perfect _)
    (tensorSquarePositive_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))
    (oneKoszulPositiveModel_support a) (oneKoszulPositiveIso a).inv
  exact he.trans (oneKoszulUnitMul_class a (unitOfInvertible (2 : R)))

lemma oneKoszulNegative_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (tensorSquareNegative (oneKoszulComplex a))
      (tensorSquareNegative_perfect _ (oneKoszulComplex_perfect a))
      (tensorSquareNegative_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))) =
    -oneKoszulClass a := by
  have he := K0WithSupport.mk_eq_of_quasiIso (oneKoszulSupport a)
    (tensorSquareNegative (oneKoszulComplex a)) (oneKoszulShiftOne a)
    (tensorSquareNegative_perfect _ (oneKoszulComplex_perfect a))
    (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
    (tensorSquareNegative_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))
    (oneKoszulNegativeModel_support a) (oneKoszulNegativeIso a).inv
  exact he.trans (oneKoszulShiftOne_class a)

lemma tensorSquareClass_oneKoszul (a : R) :
    tensorSquareClass (oneKoszulComplex a) (oneKoszulSupport a)
      (oneKoszulComplex_perfect a) (oneKoszulComplex_support a) =
    (2 : ℤ) • oneKoszulClass a := by
  have he := congrArg₂ (fun x y : K0WithSupport (oneKoszulSupport a) => x - y)
    (oneKoszulPositive_class a) (oneKoszulNegative_class a)
  exact he.trans (by simp [sub_neg_eq_add, two_smul])

/-- Axiom A4, with no locality, regularity, or non-zero-divisor assumption. -/
lemma cyclicTwo_oneKoszul (a : R) :
    cyclicTwo (oneKoszulSupport a) (oneKoszulClass a) = (2 : ℤ) • oneKoszulClass a :=
  (cyclicTwo_mk_concrete (oneKoszulSupport a) (oneKoszulComplex a)
    (oneKoszulComplex_perfect a) (oneKoszulComplex_support a)).trans
      (tensorSquareClass_oneKoszul a)

end Adams
end SerrePositivity

end KoszulNormalizationPart

section SupportNaturalityPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace Adams

lemma tensorSquareClass_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    K0WithSupport.enlarge h (tensorSquareClass P Z hp hs) =
      tensorSquareClass P W hp (hs.mono h) := by
  unfold tensorSquareClass CochainInvolution.k0Class
  rw [map_sub, K0WithSupport.enlarge_mk, K0WithSupport.enlarge_mk]
  rfl

lemma cyclicTwo_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (x : K0WithSupport Z) :
    cyclicTwo W (K0WithSupport.enlarge h x) = K0WithSupport.enlarge h (cyclicTwo Z x) := by
  have he : (cyclicTwo W).comp (K0WithSupport.enlarge h) =
      (K0WithSupport.enlarge h).comp (cyclicTwo Z) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply, K0WithSupport.enlarge_mk, cyclicTwo_mk]
    exact (tensorSquareClass_enlarge h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)).symm
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity

end SupportNaturalityPart

section BaseChangeNaturalityPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Invertible (2 : R)] [Invertible (2 : S)]
namespace Adams
variable (φ : R →+* S)

lemma tensorSquareClass_map
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) :
    K0WithSupport.map φ Z W h (tensorSquareClass P Z hp hs) =
      tensorSquareClass (baseChange φ P) W (strictlyPerfectComplex_baseChange φ P hp)
        ((hs.baseChange φ hp).mono h) := by
  let hp' := strictlyPerfectComplex_baseChange φ P hp
  let hs' := (hs.baseChange φ hp).mono h
  have hpos := K0WithSupport.mk_eq_of_quasiIso W
    (baseChange φ (tensorSquarePositive P)) (tensorSquarePositive (baseChange φ P))
    (strictlyPerfectComplex_baseChange φ _ (tensorSquarePositive_perfect P hp))
    (tensorSquarePositive_perfect _ hp')
    (((tensorSquarePositive_support hp hs).baseChange φ
      (tensorSquarePositive_perfect P hp)).mono h)
    (tensorSquarePositive_support hp' hs') (tensorSquarePositiveBaseChangeIso φ P).hom
  have hneg := K0WithSupport.mk_eq_of_quasiIso W
    (baseChange φ (tensorSquareNegative P)) (tensorSquareNegative (baseChange φ P))
    (strictlyPerfectComplex_baseChange φ _ (tensorSquareNegative_perfect P hp))
    (tensorSquareNegative_perfect _ hp')
    (((tensorSquareNegative_support hp hs).baseChange φ
      (tensorSquareNegative_perfect P hp)).mono h)
    (tensorSquareNegative_support hp' hs') (tensorSquareNegativeBaseChangeIso φ P).hom
  unfold tensorSquareClass CochainInvolution.k0Class
  rw [map_sub, K0WithSupport.map_mk, K0WithSupport.map_mk]
  exact congrArg₂ (fun a b : K0WithSupport W => a - b) hpos hneg

lemma cyclicTwo_map
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport Z) :
    K0WithSupport.map φ Z W h (cyclicTwo Z x) =
      cyclicTwo W (K0WithSupport.map φ Z W h x) := by
  have he : (K0WithSupport.map φ Z W h).comp (cyclicTwo Z) =
      (cyclicTwo W).comp (K0WithSupport.map φ Z W h) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply, cyclicTwo_mk, K0WithSupport.map_mk]
    exact tensorSquareClass_map φ Z W h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity

end BaseChangeNaturalityPart

section UnitNormalizationPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

lemma scalarModule_braiding_id :
    (β_ (ModuleCat.of R R) (ModuleCat.of R R)).hom = 𝟙 _ := by
  apply (cancel_mono (λ_ (ModuleCat.of R R)).hom).mp
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change y * x = x * y
  exact mul_comm y x

lemma oneKoszulUnitXZero_braiding_id :
    (β_ ((oneKoszulUnit (R := R)).X 0) ((oneKoszulUnit (R := R)).X 0)).hom = 𝟙 _ := by
  let e := oneKoszulUnitSelfIso (R := R)
  have : IsIso (e.hom ⊗ₘ e.hom) :=
    inferInstanceAs (IsIso (MonoidalCategory.tensorIso e e).hom)
  apply (cancel_mono (e.hom ⊗ₘ e.hom)).mp
  rw [← BraidedCategory.braiding_naturality, scalarModule_braiding_id,
    Category.comp_id, Category.id_comp]

lemma tensorSquareUnit_swap : tensorSquareSwap (oneKoszulUnit (R := R)) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      have hn : n = 0 := by dsimp at h; omega
      subst n
      rw [ιTensorObj_tensorSquareSwap]
      simp [oneKoszulUnitXZero_braiding_id]
    · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj
      exact ((tensorLeft ((oneKoszulUnit (R := R)).X 0)).map_isZero hz).eq_of_src _ _
  · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) i hi
    exact ((tensorRight ((oneKoszulUnit (R := R)).X j)).map_isZero hz).eq_of_src _ _

variable [Invertible (2 : R)]

lemma tensorSquareUnit_positive_map :
    (tensorSquarePositiveProjector (oneKoszulUnit (R := R))).map = 𝟙 _ := by
  rw [tensorSquarePositiveProjector_map, tensorSquareUnit_swap, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

lemma tensorSquareUnit_negative_map :
    (tensorSquareNegativeProjector (oneKoszulUnit (R := R))).map = 0 := by
  change 𝟙 _ - (tensorSquarePositiveProjector (oneKoszulUnit (R := R))).map = 0
  rw [tensorSquareUnit_positive_map, sub_self]

def tensorSquareUnitPositiveIso :
    tensorSquarePositive (oneKoszulUnit (R := R)) ≅ oneKoszulUnit :=
  (tensorSquarePositiveProjector oneKoszulUnit).imageIsoOfMapEqId tensorSquareUnit_positive_map ≪≫
    cochainTensorLeftUnitor oneKoszulUnit

lemma tensorSquareUnitNegative_isZero :
    IsZero (tensorSquareNegative (oneKoszulUnit (R := R))) :=
  (tensorSquareNegativeProjector oneKoszulUnit).image_isZero_of_map_eq_zero
    tensorSquareUnit_negative_map

lemma tensorSquareClass_unit_on (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hs : HasHomologySupportOn Z (oneKoszulUnit (R := R))) :
    tensorSquareClass (oneKoszulUnit (R := R)) Z oneKoszulUnit_perfect hs =
      K0WithSupport.mk Z (supportedPerfectOnObj Z oneKoszulUnit oneKoszulUnit_perfect hs) := by
  have hpos := K0WithSupport.mk_eq_of_quasiIso Z
    (tensorSquarePositive (oneKoszulUnit (R := R))) oneKoszulUnit
    (tensorSquarePositive_perfect _ oneKoszulUnit_perfect) oneKoszulUnit_perfect
    (tensorSquarePositive_support oneKoszulUnit_perfect hs) hs
    (tensorSquareUnitPositiveIso (R := R)).hom
  have hneg := K0WithSupport.mk_eq_zero_of_isZero Z
    (tensorSquareNegative_perfect _ oneKoszulUnit_perfect)
    (tensorSquareNegative_support oneKoszulUnit_perfect hs) tensorSquareUnitNegative_isZero
  have he := congrArg₂ (fun x y : K0WithSupport Z => x - y) hpos hneg
  exact he.trans (by simp)

lemma tensorSquareClass_unit :
    tensorSquareClass (oneKoszulUnit (R := R)) ⊤ oneKoszulUnit_perfect oneKoszulUnit_support =
      cyclicUnitClass :=
  tensorSquareClass_unit_on ⊤ oneKoszulUnit_support

lemma cyclicTwo_unit : cyclicTwo ⊤ (cyclicUnitClass (R := R)) = cyclicUnitClass :=
  (cyclicTwo_mk_concrete ⊤ (oneKoszulUnit (R := R)) oneKoszulUnit_perfect
    oneKoszulUnit_support).trans tensorSquareClass_unit

end Adams
end SerrePositivity

end UnitNormalizationPart

section CyclicTwoFamilyPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open TensorProduct
variable (E : Type v) [CommRing E] {R S : Type u} [CommRing R] [CommRing S]
namespace Adams
variable [Invertible (2 : R)]

def coefficientCyclicTwo (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E Z :=
  g0CoefficientMap E (cyclicTwo Z)

@[simp]
lemma coefficientCyclicTwo_tmul (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (a : E) (x : K0WithSupport Z) :
    coefficientCyclicTwo E Z (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] cyclicTwo Z x := rfl

lemma coefficientCyclicTwo_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (x : K0WithSupport.Coefficients E Z) :
    coefficientCyclicTwo E W (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h (coefficientCyclicTwo E Z x) := by
  exact g0CoefficientMap_naturality E (K0WithSupport.enlarge h) (K0WithSupport.enlarge h)
    (cyclicTwo Z) (cyclicTwo W) (cyclicTwo_enlarge h) x

lemma coefficientCyclicTwo_cup {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z) :
    coefficientCyclicTwo E (Y ⊓ Z) (K0WithSupport.coefficientCup E x y) =
      K0WithSupport.coefficientCup E (coefficientCyclicTwo E Y x) (coefficientCyclicTwo E Z y) := by
  exact coefficientPairing_naturality E K0WithSupport.cup K0WithSupport.cup
    (cyclicTwo Y) (cyclicTwo Z) (cyclicTwo (Y ⊓ Z)) cyclicTwo_cup x y

lemma coefficientCyclicTwo_map [Invertible (2 : S)] (φ : R →+* S)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport.Coefficients E Z) :
    K0WithSupport.coefficientMap E φ Z W h (coefficientCyclicTwo E Z x) =
      coefficientCyclicTwo E W (K0WithSupport.coefficientMap E φ Z W h x) := by
  exact g0CoefficientMap_naturality E (cyclicTwo Z) (cyclicTwo W)
    (K0WithSupport.map φ Z W h) (K0WithSupport.map φ Z W h) (cyclicTwo_map φ Z W h) x

def supportedCyclicTwo : SupportedAdams R E 2 where
  two_le := le_refl 2
  operation := coefficientCyclicTwo E
  enlarge := coefficientCyclicTwo_enlarge E
  cup := coefficientCyclicTwo_cup E
  unit := by rw [coefficientCyclicTwo_tmul, cyclicTwo_unit]
  koszul_one a := by
    rw [coefficientCyclicTwo_tmul, cyclicTwo_oneKoszul]
    simp only [Nat.cast_ofNat, two_smul, tmul_add]

lemma coefficientCyclicTwo_koszul {n : ℕ} (x : Fin n → R) :
    coefficientCyclicTwo E (koszulClosedSupport x) ((1 : E) ⊗ₜ[ℤ] koszulClass x) =
      (2 : E) ^ n • ((1 : E) ⊗ₜ[ℤ] koszulClass x) :=
  (supportedCyclicTwo E).koszul x

omit [CommRing S] in
/-- A source inverse for 2 supplies one in every algebra over the source. -/
@[instance_reducible]
def algebraInvertibleTwo (A : Type u) [CommRing A] [Algebra R A] : Invertible (2 : A) := by
  simpa only [map_ofNat] using Invertible.map (algebraMap R A) (2 : R)

/-- All localizations, their maps, and their model comparisons satisfy the contract. -/
def cyclicTwoFamily : LocalizationAdamsFamily R E 2 where
  atBase := supportedCyclicTwo E
  atLocalization _ A := by
    intro _ _ _
    let := algebraInvertibleTwo (R := R) A
    exact supportedCyclicTwo E
  base_naturality := by
    intro P A _ _ _ Z W h x
    let := algebraInvertibleTwo (R := R) A
    exact coefficientCyclicTwo_map E (algebraMap R A) Z W h x
  localization_naturality := by
    intro P Q A B _ _ _ _ _ _ φ _ Z W h x
    let := algebraInvertibleTwo (R := R) A
    let := algebraInvertibleTwo (R := R) B
    exact coefficientCyclicTwo_map E φ Z W h x

end Adams
end SerrePositivity

end CyclicTwoFamilyPart
