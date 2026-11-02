module

public import SerrePositivity.KTheory.Adams.TensorPower.TensorCubeClass
public import SerrePositivity.KTheory.CoefficientLinearExtension
public import SerrePositivity.KTheory.Adams.TensorPower.TensorCube
public import SerrePositivity.PerfectComplex.Eigen.CubicTensor
public import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.PerfectComplex.KoszulClasses
public import SerrePositivity.PerfectComplex.Eigen.CubicClass
public import SerrePositivity.KTheory.Adams.KoszulCubeFourierModel
public import SerrePositivity.KTheory.Adams.Family
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-! # 次数 3 の巡回 Adams 作用素

## 概要

係数を拡大した次数 3 の巡回 Adams 作用素（テンソル三乗の巡回作用の指標の像の重み付きの和）を定め、その乗法性（`cyclicThree_cup`）、台の拡大・根を保つ環の変更との自然性、スカラーの単位での回転が自明であること、単位の類と一元 Koszul 複体での正規化を示し、局所化の族の契約を満たすこと（`cyclicThreeFamily`）を与える。三次の指標の根を持つ標数零の係数体 `CubicCoefficientField` も作る。

## 方針

重みの係数は 1 の原始三乗根で、標数零の係数体で計算する。

## 規約

3 が可逆な係数で使う。

## 使われ方

IntersectionMultiplicity/Vanishing（剰余標数 2）。
-/

@[expose] public noncomputable section

universe u v

section CyclicThreePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams
variable (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
variable (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

/-- Descend the cubic evaluation to the integer Grothendieck group first. -/
def cyclicThreeValue : K0WithSupport Z →+ K0WithSupport.Coefficients E Z :=
  K0WithSupport.lift Z (tensorCubeEvaluation E t ht ζ Z)
    (tensorCubeEvaluation_iso E t ht ζ Z) (tensorCubeEvaluation_triangle E t ht ζ Z hζ)

@[simp]
lemma cyclicThreeValue_mk (X : SupportedPerfectHomotopyOn Z) :
    cyclicThreeValue E t ht ζ hζ Z (K0WithSupport.mk Z X) = tensorCubeEvaluation E t ht ζ Z X :=
  K0WithSupport.lift_mk Z (tensorCubeEvaluation E t ht ζ Z)
    (tensorCubeEvaluation_iso E t ht ζ Z) (tensorCubeEvaluation_triangle E t ht ζ Z hζ) X

@[simp]
lemma cyclicThreeValue_mk_concrete (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    cyclicThreeValue E t ht ζ hζ Z (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
      tensorCubeClass E t ht ζ P Z hp hs := cyclicThreeValue_mk E t ht ζ hζ Z _

/-- Extend the additive cubic value to an E-linear endomorphism. -/
def cyclicThree : K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E Z :=
  coefficientLinearExtension E (cyclicThreeValue E t ht ζ hζ Z)

@[simp]
lemma cyclicThree_tmul (a : E) (x : K0WithSupport Z) :
    cyclicThree E t ht ζ hζ Z (a ⊗ₜ[ℤ] x) = a • cyclicThreeValue E t ht ζ hζ Z x :=
  coefficientLinearExtension_tmul E _ a x

@[simp]
lemma cyclicThree_tmul_mk (a : E) (X : SupportedPerfectHomotopyOn Z) :
    cyclicThree E t ht ζ hζ Z (a ⊗ₜ[ℤ] K0WithSupport.mk Z X) =
      a • tensorCubeEvaluation E t ht ζ Z X := by
  rw [cyclicThree_tmul, cyclicThreeValue_mk]

lemma cyclicThree_mk_concrete (a : E) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    cyclicThree E t ht ζ hζ Z (a ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
      a • tensorCubeClass E t ht ζ P Z hp hs := cyclicThree_tmul_mk E t ht ζ hζ Z a _

lemma cyclicThreeValue_unique (F : K0WithSupport Z →+ K0WithSupport.Coefficients E Z)
    (hF : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P),
      F (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
        tensorCubeClass E t ht ζ P Z hp hs) :
    F = cyclicThreeValue E t ht ζ hζ Z := by
  apply K0WithSupport.hom_ext
  intro X
  rw [cyclicThreeValue_mk]
  exact hF (supportedPerfectRepresentative X) (supportedPerfectRepresentative_perfect X)
    (supportedPerfectRepresentative_support X)

lemma cyclicThree_unique
    (F : K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E Z)
    (hF : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P),
      F ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) =
        tensorCubeClass E t ht ζ P Z hp hs) : F = cyclicThree E t ht ζ hζ Z := by
  apply K0WithSupport.coefficientHom_ext E
  intro X
  rw [cyclicThree_tmul_mk, one_smul]
  exact hF (supportedPerfectRepresentative X) (supportedPerfectRepresentative_perfect X)
    (supportedPerfectRepresentative_support X)

end Adams
end SerrePositivity

end CyclicThreePart

section TensorCubeMultiplicativityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
namespace Adams
variable {R : Type u} [CommRing R] [Invertible (3 : R)]

lemma tensorCubeClass_tensor (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    tensorCubeClass E t ht ζ (cochainTensor P Q) (Y ⊓ Z)
      (strictlyPerfectComplex_cochainTensor P Q hp hq) (hsP.cochainTensor hsQ hp hq) =
      K0WithSupport.coefficientCup E (tensorCubeClass E t ht ζ P Y hp hsP)
        (tensorCubeClass E t ht ζ Q Z hq hsQ) := by
  let hT := strictlyPerfectComplex_cochainTensor P Q hp hq
  let sT := hsP.cochainTensor hsQ hp hq
  let hP := tensorCube_perfect P hp
  let hQ := tensorCube_perfect Q hq
  let sP := tensorCube_support hp hsP
  let sQ := tensorCube_support hq hsQ
  have he := CochainCubicAction.weightedK0Class_eq_of_quasiIso E
    (tensorCubeAction (cochainTensor P Q)) ((tensorCubeAction P).tensor (tensorCubeAction Q))
    (tensorCubeTensorIso P Q).hom (tensorCubeTensorIso_rotation P Q) t ht ζ (Y ⊓ Z)
    (tensorCube_perfect _ hT) (strictlyPerfectComplex_cochainTensor _ _ hP hQ)
    (tensorCube_support hT sT) (sP.cochainTensor sQ hP hQ)
  exact he.trans (CochainCubicAction.weightedK0Class_tensor E
    (tensorCubeAction P) (tensorCubeAction Q) t ht ζ hζ Y Z hP hQ sP sQ)

/-- Multiplicativity on all supported coefficient classes. -/
lemma cyclicThree_cup (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z) :
    cyclicThree E t ht ζ hζ (Y ⊓ Z) (K0WithSupport.coefficientCup E x y) =
      K0WithSupport.coefficientCup E (cyclicThree E t ht ζ hζ Y x)
        (cyclicThree E t ht ζ hζ Z y) := by
  have hx : ∀ (X : SupportedPerfectHomotopyOn Y) (y : K0WithSupport.Coefficients E Z),
      cyclicThree E t ht ζ hζ (Y ⊓ Z)
          (K0WithSupport.coefficientCup E ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Y X) y) =
        K0WithSupport.coefficientCup E
          (cyclicThree E t ht ζ hζ Y ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Y X))
          (cyclicThree E t ht ζ hζ Z y) := by
    intro X
    have he : (cyclicThree E t ht ζ hζ (Y ⊓ Z)).comp
        (K0WithSupport.coefficientCup E ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Y X)) =
        (K0WithSupport.coefficientCup E
          (cyclicThree E t ht ζ hζ Y ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Y X))).comp
          (cyclicThree E t ht ζ hζ Z) := by
      apply K0WithSupport.coefficientHom_ext E
      intro Q
      simp only [LinearMap.comp_apply, K0WithSupport.coefficientCup_tmul, one_mul,
        K0WithSupport.cup_mk_mk, K0WithSupport.tensorClass, cyclicThree_tmul_mk, one_smul]
      exact tensorCubeClass_tensor E t ht ζ hζ (supportedPerfectRepresentative X)
        (supportedPerfectRepresentative Q)
        (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_perfect Q)
        (supportedPerfectRepresentative_support X) (supportedPerfectRepresentative_support Q)
    intro y
    exact DFunLike.congr_fun he y
  have he : (cyclicThree E t ht ζ hζ (Y ⊓ Z)).comp
      ((K0WithSupport.coefficientCup E).flip y) =
      ((K0WithSupport.coefficientCup E).flip (cyclicThree E t ht ζ hζ Z y)).comp
        (cyclicThree E t ht ζ hζ Y) := by
    apply K0WithSupport.coefficientHom_ext E
    intro X
    exact hx X y
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity

end TensorCubeMultiplicativityPart

section TensorCubeUnitRotationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

lemma scalarTriple_cyclic (x y z : R) :
    (x ⊗ₜ[R] y) ⊗ₜ[R] z = (z ⊗ₜ[R] x) ⊗ₜ[R] y := by
  let e : (ModuleCat.of R R ⊗ ModuleCat.of R R) ⊗ ModuleCat.of R R ≅ ModuleCat.of R R :=
    MonoidalCategory.tensorIso (λ_ (ModuleCat.of R R)) (Iso.refl _) ≪≫ λ_ (ModuleCat.of R R)
  apply e.toLinearEquiv.injective
  change (x * y) * z = (z * x) * y
  ring

lemma rankOneTriple_cyclic (M : ModuleCat.{u} R) (e : M ≅ ModuleCat.of R R)
    (x y z : M) : (x ⊗ₜ[R] y) ⊗ₜ[R] z = (z ⊗ₜ[R] x) ⊗ₜ[R] y := by
  let F := MonoidalCategory.tensorIso (MonoidalCategory.tensorIso e e) e
  apply F.toLinearEquiv.injective
  change (e.hom x ⊗ₜ[R] e.hom y) ⊗ₜ[R] e.hom z =
    (e.hom z ⊗ₜ[R] e.hom x) ⊗ₜ[R] e.hom y
  exact scalarTriple_cyclic _ _ _

lemma tensorCubeUnit_rotation : tensorCubeRotation (oneKoszulUnit (R := R)) = 𝟙 _ := by
  let U := oneKoszulUnit (R := R)
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext U U U n
  intro i j k h
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      by_cases hk : k = 0
      · subst k
        have hn : n = 0 := by omega
        subst n
        apply ModuleCat.hom_ext
        apply TensorProduct.ext_threefold
        intro x y z
        change (tensorCubeRotation U).f 0
          (cochainTensorTripleι U U U 0 0 0 0 rfl ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
          cochainTensorTripleι U U U 0 0 0 0 rfl ((x ⊗ₜ[R] y) ⊗ₜ[R] z)
        rw [tensorCubeRotation_apply_ι]
        simp only [zero_add, zero_mul, Int.negOnePow_zero, one_smul]
        exact congrArg (cochainTensorTripleι U U U 0 0 0 0 rfl)
          (rankOneTriple_cyclic (U.X 0) (oneKoszulUnitSelfIso (R := R)) x y z).symm
      · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) k hk
        exact ((tensorLeft (U.X 0 ⊗ U.X 0 : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj
      exact ((tensorRight (U.X k)).map_isZero
        ((tensorLeft (U.X 0)).map_isZero hz)).eq_of_src _ _
  · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) i hi
    exact ((tensorRight (U.X k)).map_isZero
      ((tensorRight (U.X j)).map_isZero hz)).eq_of_src _ _

/-- Collapse the three scalar unit factors by the tensor unit comparisons. -/
def tensorCubeUnitIso : tensorCube (oneKoszulUnit (R := R)) ≅ oneKoszulUnit :=
  cochainTensorIso (cochainTensorLeftUnitor oneKoszulUnit) (Iso.refl _) ≪≫
    cochainTensorLeftUnitor oneKoszulUnit

end Adams
end SerrePositivity

end TensorCubeUnitRotationPart

section CubicSupportNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma tensorCubeClass_enlarge (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) :
    K0WithSupport.coefficientEnlarge E h (tensorCubeClass E t ht ζ P Z hp hs) =
      tensorCubeClass E t ht ζ P W hp (hs.mono h) := by
  unfold tensorCubeClass CochainCubicAction.weightedK0Class
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [K0WithSupport.coefficientEnlarge_tmul]
  apply congrArg (fun x => cubicCharacter ζ j ⊗ₜ[ℤ] x)
  unfold CochainCubicAction.eigenK0Class
  rw [K0WithSupport.enlarge_mk]
  rfl

lemma cyclicThreeValue_enlarge (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (x : K0WithSupport Z) :
    cyclicThreeValue E t ht ζ hζ W (K0WithSupport.enlarge h x) =
      K0WithSupport.coefficientEnlarge E h (cyclicThreeValue E t ht ζ hζ Z x) := by
  have he : (cyclicThreeValue E t ht ζ hζ W).comp (K0WithSupport.enlarge h) =
      (K0WithSupport.coefficientEnlarge E h).toAddMonoidHom.comp
        (cyclicThreeValue E t ht ζ hζ Z) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply, K0WithSupport.enlarge_mk, cyclicThreeValue_mk]
    exact (tensorCubeClass_enlarge E t ht ζ h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)).symm
  exact DFunLike.congr_fun he x

lemma cyclicThree_enlarge (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W)
    (x : K0WithSupport.Coefficients E Z) :
    cyclicThree E t ht ζ hζ W (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h (cyclicThree E t ht ζ hζ Z x) := by
  have he : (cyclicThree E t ht ζ hζ W).comp (K0WithSupport.coefficientEnlarge E h) =
      (K0WithSupport.coefficientEnlarge E h).comp (cyclicThree E t ht ζ hζ Z) := by
    apply coefficientLinearMap_ext E
    intro y
    simp only [LinearMap.comp_apply, K0WithSupport.coefficientEnlarge_tmul,
      cyclicThree_tmul, one_smul, cyclicThreeValue_enlarge E t ht ζ hζ h]
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity

end CubicSupportNaturalityPart

section CubicBaseChangeNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Invertible (3 : R)] [Invertible (3 : S)]
namespace Adams

lemma tensorCubeClass_map (E : Type v) [CommRing E] (φ : R →+* S)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (htS : (φ t) ^ 2 + φ t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) :
    K0WithSupport.coefficientMap E φ Z W h (tensorCubeClass E t ht ζ P Z hp hs) =
      tensorCubeClass E (φ t) htS ζ (baseChange φ P) W
        (strictlyPerfectComplex_baseChange φ P hp) ((hs.baseChange φ hp).mono h) := by
  let hp' := strictlyPerfectComplex_baseChange φ P hp
  let hs' := (hs.baseChange φ hp).mono h
  unfold tensorCubeClass CochainCubicAction.weightedK0Class
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [K0WithSupport.coefficientMap_tmul]
  apply congrArg (fun x => cubicCharacter ζ j ⊗ₜ[ℤ] x)
  let a := (tensorCubeAction P).characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  let b := (tensorCubeAction (baseChange φ P)).characterProjector (φ t)
    (cube_eq_one_of_cubic_relation (φ t) htS) j
  have hpa := a.image_strictlyPerfect (tensorCube_perfect P hp)
  have hpb := b.image_strictlyPerfect (tensorCube_perfect _ hp')
  have hsa := a.image_support (tensorCube_support hp hs)
  have hsb := b.image_support (tensorCube_support hp' hs')
  have he := K0WithSupport.mk_eq_of_quasiIso W (baseChange φ a.image) b.image
    (strictlyPerfectComplex_baseChange φ _ hpa) hpb ((hsa.baseChange φ hpa).mono h) hsb
    (tensorCubeCharacterBaseChangeIso φ P t (cube_eq_one_of_cubic_relation t ht) j).hom
  unfold CochainCubicAction.eigenK0Class
  rw [K0WithSupport.map_mk]
  exact he

lemma cyclicThreeValue_map (E : Type v) [CommRing E] (φ : R →+* S)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (htS : (φ t) ^ 2 + φ t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport Z) :
    K0WithSupport.coefficientMap E φ Z W h (cyclicThreeValue E t ht ζ hζ Z x) =
      cyclicThreeValue E (φ t) htS ζ hζ W (K0WithSupport.map φ Z W h x) := by
  have he : (K0WithSupport.coefficientMap E φ Z W h).toAddMonoidHom.comp
      (cyclicThreeValue E t ht ζ hζ Z) =
      (cyclicThreeValue E (φ t) htS ζ hζ W).comp (K0WithSupport.map φ Z W h) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply,
      cyclicThreeValue_mk, K0WithSupport.map_mk]
    exact tensorCubeClass_map E φ t ht htS ζ Z W h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)
  exact DFunLike.congr_fun he x

lemma cyclicThree_map (E : Type v) [CommRing E] (φ : R →+* S)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (htS : (φ t) ^ 2 + φ t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport.Coefficients E Z) :
    K0WithSupport.coefficientMap E φ Z W h (cyclicThree E t ht ζ hζ Z x) =
      cyclicThree E (φ t) htS ζ hζ W (K0WithSupport.coefficientMap E φ Z W h x) := by
  have he : (K0WithSupport.coefficientMap E φ Z W h).comp (cyclicThree E t ht ζ hζ Z) =
      (cyclicThree E (φ t) htS ζ hζ W).comp (K0WithSupport.coefficientMap E φ Z W h) := by
    apply coefficientLinearMap_ext E
    intro y
    simp only [LinearMap.comp_apply, K0WithSupport.coefficientMap_tmul,
      cyclicThree_tmul, one_smul, cyclicThreeValue_map E φ t ht htS ζ hζ Z W h]
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity

end CubicBaseChangeNaturalityPart

section CubicUnitNormalizationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma tensorCubeClass_unit_on (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hs : HasHomologySupportOn Z (oneKoszulUnit (R := R))) :
    tensorCubeClass E t ht ζ (oneKoszulUnit (R := R)) Z oneKoszulUnit_perfect hs =
      (1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z
        (supportedPerfectOnObj Z oneKoszulUnit oneKoszulUnit_perfect hs) := by
  have he := CochainCubicAction.weightedK0Class_of_map_eq_id E
    (tensorCubeAction (oneKoszulUnit (R := R))) tensorCubeUnit_rotation t ht ζ Z
    (tensorCube_perfect _ oneKoszulUnit_perfect) (tensorCube_support oneKoszulUnit_perfect hs)
  have hm := K0WithSupport.mk_eq_of_quasiIso Z (tensorCube (oneKoszulUnit (R := R)))
    oneKoszulUnit (tensorCube_perfect _ oneKoszulUnit_perfect) oneKoszulUnit_perfect
    (tensorCube_support oneKoszulUnit_perfect hs) hs (tensorCubeUnitIso (R := R)).hom
  exact he.trans (congrArg (fun x => (1 : E) ⊗ₜ[ℤ] x) hm)

lemma tensorCubeClass_unit (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) :
    tensorCubeClass E t ht ζ (oneKoszulUnit (R := R)) ⊤
      oneKoszulUnit_perfect oneKoszulUnit_support =
        (1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R)) :=
  tensorCubeClass_unit_on E t ht ζ ⊤ oneKoszulUnit_support

lemma cyclicThree_unit (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    cyclicThree E t ht ζ hζ ⊤ ((1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R))) =
      (1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R)) := by
  rw [cyclicUnitClass, cyclicThree_mk_concrete, one_smul]
  exact tensorCubeClass_unit E t ht ζ

end Adams
end SerrePositivity

end CubicUnitNormalizationPart

section CubicKoszulNormalizationPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma tensorCubeClass_oneKoszul_weight (E : Type v) [CommRing E]
    (a t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) :
    tensorCubeClass E t ht ζ (oneKoszulComplex a) (oneKoszulSupport a)
      (oneKoszulComplex_perfect a) (oneKoszulComplex_support a) =
      ((2 : E) - ζ - ζ ^ 2) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  have hf : (oneKoszulCubeFourierModelAction a t ht).map ≫
      (oneKoszulCubeFourierModelIso a t ht).hom =
      (oneKoszulCubeFourierModelIso a t ht).hom ≫ (tensorCubeAction (oneKoszulComplex a)).map :=
    (oneKoszulCubeFourierModelIso_rotation a t ht).symm
  have he := CochainCubicAction.weightedK0Class_eq_of_quasiIso E
    (oneKoszulCubeFourierModelAction a t ht) (tensorCubeAction (oneKoszulComplex a))
    (oneKoszulCubeFourierModelIso a t ht).hom hf t ht ζ (oneKoszulSupport a)
    (oneKoszulCubeFourierModel_perfect a)
    (tensorCube_perfect (oneKoszulComplex a) (oneKoszulComplex_perfect a))
    (oneKoszulCubeFourierModel_support a)
    (tensorCube_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))
  exact he.symm.trans (oneKoszulCubeFourierModel_weighted_class E a t ht ζ)

lemma tensorCubeClass_oneKoszul (E : Type v) [CommRing E]
    (a t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    tensorCubeClass E t ht ζ (oneKoszulComplex a) (oneKoszulSupport a)
      (oneKoszulComplex_perfect a) (oneKoszulComplex_support a) =
      (3 : E) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  rw [tensorCubeClass_oneKoszul_weight E a t ht ζ]
  have hc : (2 : E) - ζ - ζ ^ 2 = 3 := by linear_combination -hζ
  rw [hc]

/-- One-element normalization, valid for any scalar a in a commutative ring. -/
lemma cyclicThree_oneKoszul (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) (a : R) :
    cyclicThree E t ht ζ hζ (oneKoszulSupport a) ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) =
      (3 : E) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  rw [oneKoszulClass, cyclicThree_mk_concrete E t ht ζ hζ (oneKoszulSupport a)
    (1 : E) (oneKoszulComplex a) (oneKoszulComplex_perfect a) (oneKoszulComplex_support a),
    one_smul]
  exact tensorCubeClass_oneKoszul E a t ht ζ hζ

end Adams
end SerrePositivity

end CubicKoszulNormalizationPart

section CyclicThreeFamilyPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams
variable [Invertible (3 : R)]

def supportedCyclicThree (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) : SupportedAdams R E 3 where
  two_le := by decide
  operation := cyclicThree E t ht ζ hζ
  enlarge := cyclicThree_enlarge E t ht ζ hζ
  cup := cyclicThree_cup E t ht ζ hζ
  unit := cyclicThree_unit E t ht ζ hζ
  koszul_one := cyclicThree_oneKoszul E t ht ζ hζ

lemma cyclicThree_koszul (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) {n : ℕ} (x : Fin n → R) :
    cyclicThree E t ht ζ hζ (koszulClosedSupport x) ((1 : E) ⊗ₜ[ℤ] koszulClass x) =
      (3 : E) ^ n • ((1 : E) ⊗ₜ[ℤ] koszulClass x) :=
  (supportedCyclicThree E t ht ζ hζ).koszul x

/-- A source inverse for 3 supplies one in every algebra over the source. -/
@[instance_reducible]
def algebraInvertibleThree (A : Type u) [CommRing A] [Algebra R A] : Invertible (3 : A) := by
  simpa only [map_ofNat] using Invertible.map (algebraMap R A) (3 : R)

omit [Invertible (3 : R)] in
lemma cubicRelation_map {A : Type u} [CommRing A] (φ : R →+* A)
    (t : R) (ht : t ^ 2 + t + 1 = 0) : (φ t) ^ 2 + φ t + 1 = 0 := by
  simpa only [map_add, map_pow, map_one, map_zero] using congrArg φ ht

/-- The same cubic operation on every localization model, with explicit root transport. -/
def cyclicThreeFamily (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) : LocalizationAdamsFamily R E 3 where
  atBase := supportedCyclicThree E t ht ζ hζ
  atLocalization _ A := by
    intro _ _ _
    let := algebraInvertibleThree (R := R) A
    exact supportedCyclicThree E (algebraMap R A t) (cubicRelation_map (algebraMap R A) t ht) ζ hζ
  base_naturality := by
    intro P A _ _ _ Z W h x
    let := algebraInvertibleThree (R := R) A
    exact cyclicThree_map E (algebraMap R A) t ht (cubicRelation_map (algebraMap R A) t ht)
      ζ hζ Z W h x
  localization_naturality := by
    intro P Q A B _ _ _ _ _ _ φ hφ Z W h x
    let := algebraInvertibleThree (R := R) A
    let := algebraInvertibleThree (R := R) B
    have he : φ (algebraMap R A t) = algebraMap R B t := DFunLike.congr_fun hφ t
    have hn := cyclicThree_map E φ (algebraMap R A t)
      (cubicRelation_map (algebraMap R A) t ht)
      (cubicRelation_map φ (algebraMap R A t) (cubicRelation_map (algebraMap R A) t ht))
      ζ hζ Z W h x
    simpa only [supportedCyclicThree, he] using hn

end Adams
end SerrePositivity

end CyclicThreeFamilyPart

section CubicCoefficientFieldPart

namespace SerrePositivity
namespace Adams

abbrev CubicCoefficientField := CyclotomicField 3 ℚ

local instance : IsCyclotomicExtension {3} ℚ CubicCoefficientField :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

def cubicCoefficientRoot : CubicCoefficientField :=
  Classical.choose (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ CubicCoefficientField
    (S := ({3} : Set ℕ)) (n := 3) (by simp) (by decide))

lemma cubicCoefficientRoot_primitive : IsPrimitiveRoot cubicCoefficientRoot 3 := by
  unfold cubicCoefficientRoot
  exact Classical.choose_spec (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ CubicCoefficientField
    (S := ({3} : Set ℕ)) (n := 3) (by simp) (by decide))

lemma cubicCoefficientRoot_relation : cubicCoefficientRoot ^ 2 + cubicCoefficientRoot + 1 = 0 := by
  have hp := cubicCoefficientRoot_primitive.pow_eq_one
  have hn := cubicCoefficientRoot_primitive.ne_one (by decide)
  have he : (cubicCoefficientRoot - 1) *
      (cubicCoefficientRoot ^ 2 + cubicCoefficientRoot + 1) = 0 := by
    calc
      _ = cubicCoefficientRoot ^ 3 - 1 := by ring
      _ = 0 := by rw [hp, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hn)

end Adams
end SerrePositivity

end CubicCoefficientFieldPart
