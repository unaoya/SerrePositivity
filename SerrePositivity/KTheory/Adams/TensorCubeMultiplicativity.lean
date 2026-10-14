module

public import SerrePositivity.KTheory.Adams.TensorCubeTensor
public import SerrePositivity.KTheory.Adams.CyclicThree
public import SerrePositivity.PerfectComplex.CubicActionTensorClass

/-! # Multiplicativity of weighted cyclic tensor cubes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
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

omit [Invertible (3 : R)] in
private lemma coefficientHom_ext (E : Type v) [CommRing E]
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {B : Type*} [AddCommGroup B] [Module E B]
    (F G : K0WithSupport.Coefficients E Z →ₗ[E] B)
    (h : ∀ X : SupportedPerfectHomotopyOn Z,
      F ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z X) =
        G ((1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z X)) : F = G := by
  let η : K0WithSupport Z →+ K0WithSupport.Coefficients E Z :=
    (TensorProduct.mk ℤ E (K0WithSupport Z) (1 : E)).toAddMonoidHom
  have he : F.toAddMonoidHom.comp η = G.toAddMonoidHom.comp η := by
    apply K0WithSupport.hom_ext
    exact h
  apply AlgebraTensorModule.ext
  intro a x
  have hx : a ⊗ₜ[ℤ] x = a • ((1 : E) ⊗ₜ[ℤ] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hx, F.map_smul, G.map_smul]
  exact congrArg (fun y => a • y) (DFunLike.congr_fun he x)

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
      apply coefficientHom_ext E
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
    apply coefficientHom_ext E
    intro X
    exact hx X y
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity
