module

public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulBounds
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.HomologicalAlgebra.BoundedKoszulAugmentation
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulAugmentationZero
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulTermColimit
public import SerrePositivity.HomologicalAlgebra.KoszulRadicalSupport
public import SerrePositivity.CommutativeAlgebra.Idempotent
public import SerrePositivity.HomologicalAlgebra.TorCoefficientIdeal
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite
public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison
public import Mathlib.RingTheory.Ideal.Colon

/-! # パラメータの Koszul ホモロジーと Tor の係数作用の零化

## 概要

反復したスカラー錐のホモロジーを零化するイデアルの冪を明示し、パラメータ列の Koszul 複体の余極限と Koszul 複体の比較（擬同型）から、高次 Tor の零化イデアルの冪が Koszul ホモロジーを零化することを示す。冪等なイデアルでは冪を外せる。有限段のパラメータの正次数の Koszul ホモロジーの零化、有限自由な比較や almost な比較（どちらの向きでも）を通じた Tor の係数作用 `torCoefficientScalar` の零化を与える。

## 方針

零化は完全列の両端の零化イデアルの積で抑え、錐を反復するたびに一つずつ掛ける。Tor の係数作用の零化はスカラーの分解と三重積で移す。

## 規約

`torCoefficientScalar` 系の名前は CLMST が参照する。

## 使われ方

CLMST の有限段の Koszul の零化と完備テンソルの比較。
-/

@[expose] public noncomputable section

universe u

section KoszulHomologyAnnihilatorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- In an exact three-term sequence the product of endpoint annihilators kills the middle. -/
lemma ideal_mul_le_annihilator_of_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact)
    (I J : Ideal R) (hI : I ≤ Module.annihilator R S.X₁)
    (hJ : J ≤ Module.annihilator R S.X₃) : I * J ≤ Module.annihilator R S.X₂ := by
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro x
  have hx : S.g (b • x) = 0 := by
    rw [map_smul]
    exact (Module.mem_annihilator.mp (hJ hb)) _
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS (b • x) hx
  rw [mul_smul, ← hy, ← map_smul, Module.mem_annihilator.mp (hI ha) y, map_zero]

/-- Adjacent endpoint annihilators multiply along the actual mapping-cone long exact sequence. -/
lemma mappingCone_homology_annihilator_mul
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (q : ℤ)
    (I J : Ideal R) (hI : I ≤ Module.annihilator R (L.homology q))
    (hJ : J ≤ Module.annihilator R (K.homology (q + 1))) :
    I * J ≤ Module.annihilator R ((CochainComplex.mappingCone f).homology q) :=
  ideal_mul_le_annihilator_of_exact _ (Cone.exact₃ f q (q + 1) rfl) I J hI hJ

/-- Each parameter scalar cone doubles the sufficient ideal-power exponent on low homology. -/
lemma koszulComplexOn_homology_annihilator_pow
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (b : ℤ)
    (hK : ∀ q, q < b → I ≤ Module.annihilator R (K.homology q)) :
    ∀ {r : ℕ} (y : Fin r → R) (q : ℤ), q < b - (r : ℤ) →
      I ^ (2 ^ r) ≤ Module.annihilator R ((koszulComplexOn y K).homology q)
  | 0, _, q, hq => by
    change I ^ (2 ^ 0) ≤ Module.annihilator R (K.homology q)
    simpa only [pow_zero, pow_one] using hK q (by simpa using hq)
  | r + 1, y, q, hq => by
    have h₀ := koszulComplexOn_homology_annihilator_pow K I b hK (Fin.init y) q
      (by omega)
    have h₁ := koszulComplexOn_homology_annihilator_pow K I b hK (Fin.init y) (q + 1)
      (by omega)
    have h := mappingCone_homology_annihilator_mul
      (smulId (y (Fin.last r)) (koszulComplexOn (Fin.init y) K)) q _ _ h₀ h₁
    have hpow : I ^ (2 ^ (r + 1)) = I ^ (2 ^ r) * I ^ (2 ^ r) := by
      rw [pow_succ (2 : ℕ) r, pow_mul, pow_two]
    rw [hpow]
    exact h

/-- Full higher-Tor annihilation gives an explicit power on the actual parameter/colimit model. -/
lemma parameterKoszulColimit_homology_annihilator_pow_of_tor_annihilated
    {C : Type u} [CommRing C] [Algebra R C] [IsNoetherian R R]
    {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    {r : ℕ} (y : Fin r → C) (q : ℤ) (hq : q < (e : ℤ) - (r : ℤ)) :
    I ^ (2 ^ r) ≤ Module.annihilator C
      (((parameterKoszulColimitFunctor z y).obj (ModuleCat.of C C)).homology q) := by
  apply koszulComplexOn_homology_annihilator_pow _ I (e : ℤ) _ y q hq
  intro j hj
  by_cases hneg : j < 0
  · have hz := (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj
        (ModuleCat.of C C)).sc j).isZero_homology_of_isZero_X₂
      (algebraKoszulDualIntegerColimit_isZero_X_of_neg z (ModuleCat.of C C) j hneg)
    have : Subsingleton
        (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj
          (ModuleCat.of C C)).homology j) := ModuleCat.subsingleton_of_isZero hz
    intro c hc
    rw [Module.mem_annihilator]
    intro x
    exact Subsingleton.elim _ _
  · have heq : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
    rw [← heq]
    exact algebraKoszulDualIntegerColimitHomology_annihilator_of_tor_annihilated
      z hres I hTor j.toNat (by omega)

end SerrePositivity

end KoszulHomologyAnnihilatorPart

section ParameterKoszulComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {e r : ℕ} (z : Fin e → R) (y : Fin r → C)

/-- The actual canonical augmentation becomes a quasi-isomorphism after arbitrary parameter
Koszul operators when the standard coordinate images lie in the parameter radical. -/
lemma parameterKoszulColimitToKoszul_quasiIso
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (M : ModuleCat.{u} C) : QuasiIso ((parameterKoszulColimitToKoszul z y).app M) := by
  change QuasiIso ((koszulFunctor y).map
    ((algebraKoszulDualIntegerToSingle (C := C) z).app M))
  apply boundedKoszulAugmentation_quasiIso y _ M _ e
  · exact algebraKoszulDualIntegerColimit_isZero_X_of_neg z M
  · exact algebraKoszulDualIntegerColimit_isZero_X_of_gt z M
  · intro q hq p
    have hNat : 0 < q.toNat := by omega
    have h := algebraKoszulDualColimit_positive_term_koszulHomology_isZero
      z y hz M (q.toNat - 1) p
    rw [Nat.sub_add_cancel (by omega : 1 ≤ q.toNat)] at h
    exact h.of_iso
      (((koszulModuleFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).mapIso
        (((algebraKoszulDualColimitFunctor (C := C) z).obj M).extendXIso
          nonnegativeCochainEmbedding (i := q.toNat) (by
            change (q.toNat : ℤ) = q
            exact Int.toNat_of_nonneg (by omega))))

/-- The comparison is natural in actual C-module coefficients and uses the actual standard map. -/
def parameterKoszulColimitHomologyNatIso
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical) (q : ℤ) :
    parameterKoszulColimitFunctor z y ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) q ≅
      koszulModuleFunctor y ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) q := by
  have : ∀ M : ModuleCat.{u} C,
      IsIso ((Functor.whiskerRight (parameterKoszulColimitToKoszul z y)
        (homologyFunctor (ModuleCat.{u} C) (.up ℤ) q)).app M) := fun M => by
    have := parameterKoszulColimitToKoszul_quasiIso z y hz M
    change IsIso (homologyMap ((parameterKoszulColimitToKoszul z y).app M) q)
    infer_instance
  have := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (parameterKoszulColimitToKoszul z y)
      (homologyFunctor (ModuleCat.{u} C) (.up ℤ) q))
  exact asIso (Functor.whiskerRight (parameterKoszulColimitToKoszul z y)
    (homologyFunctor (ModuleCat.{u} C) (.up ℤ) q))

/-- Full higher-Tor annihilation transfers to the actual arbitrary-parameter Koszul homology,
with the explicit positive exponent supplied by the scalar-cone induction. -/
lemma parameterKoszulHomology_annihilator_pow_of_tor_annihilated [IsNoetherian R R]
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (q : ℤ) (hq : q < (e : ℤ) - (r : ℤ)) :
    I ^ (2 ^ r) ≤ Module.annihilator C (((koszulModuleFunctor y).obj
      (ModuleCat.of C C)).homology q) := by
  have hpow := parameterKoszulColimit_homology_annihilator_pow_of_tor_annihilated
    z hres I hTor y q hq
  let E := ((parameterKoszulColimitHomologyNatIso z y hz q).app
    (ModuleCat.of C C)).toLinearEquiv
  intro c hc
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨v, rfl⟩ := E.surjective x
  rw [← E.map_smul, Module.mem_annihilator.mp (hpow hc), E.map_zero]

end SerrePositivity

end ParameterKoszulComparisonPart

section ParameterKoszulIdempotentPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C] [IsNoetherian R R]
/-- Quotient-image idempotence removes the finite-cone annihilator exponent. -/
lemma parameterKoszulHomology_annihilator_of_tor_and_idempotent
    {e r : ℕ} (z : Fin e → R) (y : Fin r → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (a : C) (ha : a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (q : ℤ) (hq : q < (e : ℤ) - (r : ℤ)) :
    I ≤ Module.annihilator C (((koszulModuleFunctor y).obj (ModuleCat.of C C)).homology q) := by
  have hpow := parameterKoszulHomology_annihilator_pow_of_tor_annihilated
    z y hz hres I hTor q hq
  obtain ⟨n, _, hn⟩ := koszulModuleHomology_uniform_power_annihilator_of_mem_radical
    (RingHom.id C) y a ha
  intro c hc
  rw [Module.mem_annihilator]
  apply ideal_annihilates_of_pow_annihilates_and_powerTorsion I a hI (2 ^ r)
    (pow_pos (by decide) r)
    (fun b hb x => Module.mem_annihilator.mp (hpow hb) x)
    (fun x => ⟨n, Module.mem_annihilator.mp (hn (ModuleCat.of C C) q) x⟩) c hc

/-- Every positive Koszul homology of a length-e sequence is killed by the ideal itself. -/
lemma parameterKoszulPositiveHomology_annihilator_of_tor_and_idempotent
    {e : ℕ} (z : Fin e → R) (y : Fin e → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (a : C) (ha : a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (i : ℕ) (hi : 0 < i) :
    I ≤ Module.annihilator C (koszulHomologySelf y i) := by
  have h := parameterKoszulHomology_annihilator_of_tor_and_idempotent
    z y hz hres I hTor a ha hI (-(i : ℤ)) (by omega)
  change I ≤ Module.annihilator C
    ((koszulComplexOn y ((HomologicalComplex.single (ModuleCat.{u} C) (.up ℤ) 0).obj
      (ModuleCat.of C C))).homology (-(i : ℤ))) at h
  rw [koszulComplexOn_single] at h
  exact h

/-- The image ideal kills every positive actual Koszul homology for equal-length sequences. -/
lemma parameterKoszulPositiveHomology_imageIdeal_annihilator_of_tor_and_idempotent
    {S : Type u} [CommRing S] (φ : S →+* C) (I : Ideal S) (a : S)
    {e : ℕ} (z : Fin e → R) (y : Fin e → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (φ s) = 0)
    (ha : φ a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (i : ℕ) (hi : 0 < i) :
    I.map φ ≤ Module.annihilator C (koszulHomologySelf y i) := by
  apply parameterKoszulPositiveHomology_annihilator_of_tor_and_idempotent z y hz hres
    (I.map φ) _ (φ a) ha (quotient_power_images_idempotent_baseChange φ I a hI) i hi
  intro N j hj
  exact torCoefficientScalarEndomorphism_mapIdeal_eq_zero φ I N j (hTor N j hj)

/-- Restriction along the original map gives the base-ideal annihilator used in applications. -/
lemma parameterKoszulPositiveHomology_restricted_annihilator_of_tor_and_idempotent
    {S : Type u} [CommRing S] (φ : S →+* C) (I : Ideal S) (a : S)
    {e : ℕ} (z : Fin e → R) (y : Fin e → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (φ s) = 0)
    (ha : φ a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (i : ℕ) (hi : 0 < i) :
    let _ := Module.compHom (koszulHomologySelf y i) φ
    I ≤ Module.annihilator S (koszulHomologySelf y i) := by
  let _ := Module.compHom (koszulHomologySelf y i) φ
  change I ≤ Module.annihilator S (koszulHomologySelf y i)
  have h := parameterKoszulPositiveHomology_imageIdeal_annihilator_of_tor_and_idempotent
    φ I a z y hz hres hTor ha hI i hi
  intro s hs
  rw [Module.mem_annihilator]
  intro x
  exact Module.mem_annihilator.mp (h (Ideal.mem_map_of_mem φ hs)) x

end SerrePositivity

end ParameterKoszulIdempotentPart

section FiniteParameterKoszulAnnihilatorPart

namespace SerrePositivity
open CategoryTheory

/-- A finite injective local extension supplies the parameter support conditions. The
annihilator is the original base ideal, acting by restriction along its actual coefficient map.
The distinguished scalar is allowed to be any one of the standard coordinates. -/
lemma finiteParameterKoszul_positive_annihilator
    {R D E C S : Type u} [CommRing R] [CommRing D] [CommRing E] [CommRing C] [CommRing S]
    [IsNoetherian R R] [IsLocalRing D] [IsLocalRing E]
    [Algebra R D] [Algebra D E] [Module.Finite D E] [Algebra R C]
    (hinj : Function.Injective (algebraMap D E)) (φ : E →+* C)
    (hφ : ∀ x : R, φ (algebraMap D E (algebraMap R D x)) = algebraMap R C x)
    {e : ℕ} (z : Fin e → R)
    (hz : IsSystemOfParameters D (algebraMap R D ∘ z))
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (ψ : S →+* C) (I : Ideal S) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap R C (z j₀))
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0)
    (y : Fin e → E) (hy : IsSystemOfParameters E y) (i : ℕ) (hi : 0 < i) :
    let _ := Module.compHom (koszulHomologySelf (φ ∘ y) i) ψ
    I ≤ Module.annihilator S (koszulHomologySelf (φ ∘ y) i) := by
  have hsupport : ∀ j, algebraMap R C (z j) ∈
      (Ideal.span (Set.range (φ ∘ y))).radical := by
    intro j
    simpa only [Function.comp_apply, hφ] using
      hz.finite_map_coordinates_mem_radical hinj hy φ j
  exact parameterKoszulPositiveHomology_restricted_annihilator_of_tor_and_idempotent
    ψ I a z (φ ∘ y) hsupport hres hTor (by rw [ha]; exact hsupport j₀) hI i hi

end SerrePositivity

end FiniteParameterKoszulAnnihilatorPart

section TorFiniteFreeComparisonAnnihilatorPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- Kernel and cokernel annihilators kill positive Tor by their product.
The coefficient ring C need not be finite; the test module N is arbitrary. -/
lemma torCoefficientScalar_eq_zero_of_finiteFree_comparison
    (r : ℕ) (f : C →ₗ[R] (Fin r → R)) (a b : R)
    (ha : ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hb : ∀ x : f.ker, b • x = 0)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C (a * b)) = 0 := by
  obtain ⟨v, hv⟩ := exists_scalar_factorization_through_finiteFree r f a b ha hb
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  have hz : IsZero (F.obj (ModuleCat.of R (Fin r → R))) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) (Fin r → R) N j)
  have hm : ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C (a * b))) =
      (ModuleCat.ofHom f) ≫ (ModuleCat.ofHom v) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hv x
    change v (f x) = (a * b) • x at h
    change algebraMap R C (a * b) * x = v (f x)
    simpa only [Algebra.smul_def] using h.symm
  change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C (a * b)))) = 0
  rw [hm, CategoryTheory.Functor.map_comp, hz.eq_of_tgt (F.map (ModuleCat.ofHom f)) 0,
    zero_comp]

/-- An annihilator of the test module acts by the original coefficient scalar as zero on Tor. -/
lemma torCoefficientScalar_algebraMap_eq_zero_of_annihilates
    (N : ModuleCat.{u} R) (i : ℕ) (a : R) (ha : ∀ x : N, a • x = 0) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0 := by
  apply (torAlgebraComparison_scalar_zero_iff_forall N i (algebraMap R C a)).mpr
  intro x
  exact torAlg_smul_eq_zero (algebraMap R C) i N a ha x

/-- An ideal annihilating kernel and cokernel acts by its square as zero on every positive Tor. -/
lemma torCoefficientScalar_eq_zero_of_finiteFree_ideal_square
    (r : ℕ) (f : C →ₗ[R] (Fin r → R)) (I : Ideal R)
    (hc : ∀ a ∈ I, ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hk : ∀ b ∈ I, ∀ x : f.ker, b • x = 0)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ I * I) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  have hsq : I * I ≤ (coefficientFunctorAnnihilator (C := C) F).comap (algebraMap R C) := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    exact torCoefficientScalar_eq_zero_of_finiteFree_comparison r f a b (hc a ha) (hk b hb) N i hi
  exact hsq hs

/-- Modulo an annihilator of the test module, idempotence removes the square loss.
All positive degrees and arbitrary test modules are retained. -/
lemma torCoefficientScalar_eq_zero_of_finiteFree_almost_comparison
    (r : ℕ) (f : C →ₗ[R] (Fin r → R)) (I : Ideal R)
    (hc : ∀ a ∈ I, ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hk : ∀ b ∈ I, ∀ x : f.ker, b • x = 0)
    (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a}))))
    (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ I) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  let J := (coefficientFunctorAnnihilator (C := C) F).comap (algebraMap R C)
  have hK : Ideal.span {a} ≤ J := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i a ha
  have hsq : I * I ≤ J := by
    intro x hx
    exact torCoefficientScalar_eq_zero_of_finiteFree_ideal_square r f I hc hk N i hi x hx
  have hI := ideal_le_pow_sup_of_quotient_image_idempotent I (Ideal.span {a}) 2 (by decide) hid
  exact hI.trans (sup_le (by simpa only [pow_two] using hsq) hK) hs

end SerrePositivity

end TorFiniteFreeComparisonAnnihilatorPart

section TorAlmostComparisonTransportPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D]

private lemma torScalar_zero_of_scalar_factorization
    (f : C →ₗ[R] D) (v : D →ₗ[R] C) (r c : R)
    (hv : f.comp v = r • LinearMap.id)
    (N : ModuleCat.{u} R) (i : ℕ)
    (hc : torCoefficientScalarEndomorphism C N i (algebraMap R C c) = 0) :
    torCoefficientScalarEndomorphism D N i (algebraMap R D (r * c)) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  have hm : ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R D (r * c))) =
      (ModuleCat.ofHom v) ≫
        (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C c))) ≫ ModuleCat.ofHom f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hv x
    change f (v x) = r • x at hh
    change algebraMap R D (r * c) * x = f (algebraMap R C c * v x)
    rw [← Algebra.smul_def (r * c) x, ← Algebra.smul_def c (v x), f.map_smul, hh, smul_smul]
    rw [mul_comm r c]
  change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R D (r * c)))) = 0
  change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C c))) = 0 at hc
  rw [hm, Functor.map_comp, Functor.map_comp, hc, zero_comp, comp_zero]

private lemma torIdeal_zero_of_triple_products
    (I : Ideal R) (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a})))) (i : ℕ)
    (hprod : ∀ x ∈ I, ∀ y ∈ I, ∀ z ∈ I,
      torCoefficientScalarEndomorphism D N i (algebraMap R D (x * y * z)) = 0) :
    ∀ s ∈ I, torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  let J := (coefficientFunctorAnnihilator (C := D) F).comap (algebraMap R D)
  have hcolon : I * I ≤ J.colon (I : Set R) := by
    apply Ideal.mul_le.mpr
    intro x hx y hy
    apply Submodule.mem_colon.mpr
    intro z hz
    exact hprod x hx y hy z hz
  have hcube : I ^ 3 ≤ J := by
    rw [show I ^ 3 = (I * I) * I by simp only [pow_succ, pow_zero, one_mul]]
    apply Ideal.mul_le.mpr
    intro x hx z hz
    exact Submodule.mem_colon.mp (hcolon hx) z hz
  have haJ : Ideal.span {a} ≤ J := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i a ha
  have hI := ideal_le_pow_sup_of_quotient_image_idempotent I (Ideal.span {a}) 3 (by decide) hid
  exact hI.trans (sup_le hcube haJ)

/-- An actual comparison with almost-zero kernel and cokernel preserves the entire
ideal's zero action on original Tor, in both directions and in every degree.
The test module is arbitrary apart from its stated annihilator. -/
theorem torCoefficientIdeal_eq_zero_iff_of_almost_comparison
    (f : C →ₗ[R] D) (I : Ideal R)
    (hk : ∀ a ∈ I, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ I, ∀ y : D ⧸ f.range, b • y = 0)
    (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a})))) (i : ℕ) :
    (∀ s ∈ I, torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
      ∀ s ∈ I, torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  constructor
  · intro hC
    apply torIdeal_zero_of_triple_products I N a ha hid i
    intro x hx y hy z hz
    obtain ⟨v, _hC, hD⟩ := exists_scalar_inverse_of_ker_coker_annihilated f x y (hk x hx) (hc y hy)
    exact torScalar_zero_of_scalar_factorization f v (x * y) z hD N i (hC z hz)
  · intro hD
    apply torIdeal_zero_of_triple_products I N a ha hid i
    intro x hx y hy z hz
    obtain ⟨v, hC, _hD⟩ := exists_scalar_inverse_of_ker_coker_annihilated f x y (hk x hx) (hc y hy)
    exact torScalar_zero_of_scalar_factorization v f (x * y) z hC N i (hD z hz)

/-- A reverse finite-free comparison also supplies all positive Tor zero actions.
There is no requirement for a single almost-isomorphism pointing from C to the free module. -/
theorem torCoefficientScalar_eq_zero_of_reverse_finiteFree_almost_comparison
    (r : ℕ) (f : (Fin r → R) →ₗ[R] C) (I : Ideal R)
    (hk : ∀ a ∈ I, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ I, ∀ y : C ⧸ f.range, b • y = 0)
    (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a}))))
    (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ I) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  have hz : IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R (Fin r → R))).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) (Fin r → R) N j)
  have hfree : ∀ x ∈ I,
      torCoefficientScalarEndomorphism (Fin r → R) N i
        (algebraMap R (Fin r → R) x) = 0 :=
    fun _ _ => hz.eq_of_src _ _
  exact ((torCoefficientIdeal_eq_zero_iff_of_almost_comparison
    f I hk hc N a ha hid i).mp hfree) s hs

end SerrePositivity

end TorAlmostComparisonTransportPart
