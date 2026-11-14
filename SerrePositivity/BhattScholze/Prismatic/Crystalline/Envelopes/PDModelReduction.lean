module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDInclusion
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 結晶 pd Čech 模型の mod p

## 概要
整係数の完備 pd Čech 模型の剰余と、標数 p の係数上で作った完備模型を比較する。

## 方針
単項式基底で未完備模型の係数の剰余を取り、完備化の単位を経由する。

## 規約
係数変換は結晶基底からその剰余体への商写像に沿う。

## 使われ方
pd de Rham 比較と Bockstein の生成元の照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "K" => crystallineBase p
local notation "k" => cartierBase p
local notation "Raw" => pdRawModel K r ⋙ Under.forget (CommRingCat.of K)
local notation "Res" => pdRawModel k r ⋙ Under.forget (CommRingCat.of k)

private theorem pdRaw_regular (n : ℕ) :
    IsSMulRegular (pdRaw (crystallineBase.{u} p) r n) (p : pdRaw K r n) := by
  intro x y h
  apply (pdRawBasis K r n).repr.injective
  apply Finsupp.ext
  intro m
  apply crystallineBase_regular p
  change (p : pdRaw K r n) * x = (p : pdRaw K r n) * y at h
  rw [← map_natCast (algebraMap K (pdRaw K r n)), ← Algebra.smul_def, ← Algebra.smul_def] at h
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
    congrArg (fun z => (pdRawBasis K r n).repr z m) h

private def rawUnit (L : Type u) [CommRing L] :
    pdRawModel L r ⋙ Under.forget (CommRingCat.of L) ⟶
      pdModel p L r ⋙ Under.forget (CommRingCat.of L) where
  app n := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw L r n.len))
  naturality _ _ θ := (ringCatMap_comp_unit p ((pdRawModel L r).map θ).right).symm

private theorem integralUnit_modPrime_isIso :
    IsIso (modPrimeMap p (rawUnit p r (crystallineBase.{u} p))) := by
  let h (n : SimplexCategory) :
      IsIso ((modPrimeMap p (rawUnit p r (crystallineBase.{u} p))).app n) :=
    crystallinePrincipalCompletionUnit_isIso_modPrime p (CommRingCat.of (pdRaw K r n.len))
      (pdRaw_regular p r n.len)
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h

private theorem residualUnit_isIso : IsIso (rawUnit p r (cartierBase.{u} p)) := by
  let h (n : SimplexCategory) : IsIso ((rawUnit p r (cartierBase.{u} p)).app n) := by
    have hp : (p : pdRaw (cartierBase.{u} p) r n.len) = 0 := by
      rw [← map_natCast (algebraMap (cartierBase p) (pdRaw (cartierBase p) r n.len)),
        cartierBase_natCast, map_zero]
    let := principalCompletionCommRing (pdRaw (cartierBase.{u} p) r n.len) (p : pdRaw k r n.len)
    exact ((crystallinePrincipalCompletionOfZero _ hp).symm.toCommRingCatIso).isIso_hom
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h

private theorem rawCoefficients_surjective (n : ℕ) :
    Function.Surjective (pdRawCoefficients (crystallineBase.{u} p) k r n) := by
  intro y
  let b := pdRawBasis (crystallineBase.{u} p) r n
  let c := pdRawBasis (cartierBase.{u} p) r n
  obtain ⟨x, hx⟩ := Finsupp.mapRange_surjective (algebraMap K k) (map_zero _)
    Ideal.Quotient.mk_surjective (c.repr y)
  refine ⟨b.repr.symm x, c.repr.injective ?_⟩
  rw [pdRawCoefficients_repr]
  change freeDPCoefficientMap _ K k (b.repr (b.repr.symm x)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact hx

private theorem rawCoefficients_ker (n : ℕ) :
    RingHom.ker (pdRawCoefficients (crystallineBase.{u} p) k r n).toRingHom =
      Ideal.span {(p : pdRaw K r n) ^ (1 : ℕ)} := by
  classical
  rw [pow_one]
  ext x
  change pdRawCoefficients (crystallineBase.{u} p) k r n x = 0 ↔ _
  constructor
  · intro hx
    let b := pdRawBasis (crystallineBase.{u} p) r n
    let c := pdRawBasis (cartierBase.{u} p) r n
    have hc (m) : (p : K) ∣ b.repr x m := by
      have h := congrArg (fun y => c.repr y m) hx
      simp only [c, pdRawCoefficients_repr, map_zero, Finsupp.zero_apply] at h
      have hq : Ideal.Quotient.mk (crystallineBasePrism.{u} p).ideal (b.repr x m) = 0 := h
      have hm := Ideal.Quotient.eq_zero_iff_mem.mp hq
      change b.repr x m ∈ Ideal.span {(crystallineBasePrism.{u} p).generator} at hm
      rw [crystallineBase_generator, Ideal.mem_span_singleton] at hm
      exact hm
    choose f hf using hc
    let z := Finsupp.onFinset (b.repr x).support
      (fun m => if m ∈ (b.repr x).support then f m else 0)
      (fun m hm => by by_contra hn; exact hm (ite_eq_right hn))
    refine Ideal.mem_span_singleton.mpr ⟨b.repr.symm z, ?_⟩
    apply b.repr.injective
    rw [← map_natCast (algebraMap K (pdRaw K r n)), ← Algebra.smul_def, map_smul,
      LinearEquiv.apply_symm_apply]
    apply Finsupp.ext
    intro m
    simp only [z, Finsupp.smul_apply, Finsupp.onFinset_apply, smul_eq_mul]
    by_cases hm : m ∈ (b.repr x).support
    · rw [ite_eq_left hm, ← hf m]
    · rw [ite_eq_right hm, mul_zero, Finsupp.notMem_support_iff.mp hm]
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, map_natCast, ← map_natCast (algebraMap k (pdRaw k r n)),
      cartierBase_natCast, map_zero, zero_mul]

private def rawReductionApp (n : SimplexCategory) :
    (modPrimeCosimplicial p (Raw)).obj n ⟶ (Res).obj n :=
  CommRingCat.ofHom (Ideal.Quotient.lift _
    (pdRawCoefficients K k r n.len).toRingHom fun _ hx =>
      RingHom.mem_ker.mp (rawCoefficients_ker p r n.len ▸ hx))

private def rawReduction :
    modPrimeCosimplicial p (Raw : CosimplicialObject CommRingCat.{u}) ⟶ Res where
  app := rawReductionApp p r
  naturality m n θ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ConcreteCategory.congr_hom ((pdRawChange K k r).naturality θ) x

private theorem rawReduction_isIso : IsIso (rawReduction.{u} p r) := by
  let h (n : SimplexCategory) : IsIso ((rawReduction.{u} p r).app n) := by
    have hj : Function.Injective (rawReductionApp.{u} p r n).hom :=
      (Ideal.injective_lift_iff _).mpr (rawCoefficients_ker p r n.len)
    have hs : Function.Surjective (rawReductionApp.{u} p r n) := by
      intro y
      obtain ⟨x, hx⟩ := rawCoefficients_surjective p r n.len y
      exact ⟨Ideal.Quotient.mk _ x, hx⟩
    let e := RingEquiv.ofBijective (rawReductionApp.{u} p r n).hom ⟨hj, hs⟩
    exact e.toCommRingCatIso.isIso_hom
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h

/-- 整係数の完備 pd Čech 模型の mod p は標数 p の完備 pd Čech 模型。 -/
def pdModel_modP :
    modPrimeCosimplicial p (pdRings.{u} p r) ≅
      pdModel p (cartierBase.{u} p) r ⋙ Under.forget (CommRingCat.of k) := by
  letI := integralUnit_modPrime_isIso.{u} p r
  letI := rawReduction_isIso.{u} p r
  letI := residualUnit_isIso.{u} p r
  exact (asIso (modPrimeMap p (rawUnit p r K))).symm ≪≫ asIso (rawReduction p r) ≪≫
    asIso (rawUnit p r k)

end SerrePositivity.BhattScholze.Prismatic
