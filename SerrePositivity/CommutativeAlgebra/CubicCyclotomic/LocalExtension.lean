module

public import SerrePositivity.CommutativeAlgebra.CubicCyclotomic.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.FlatBaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.Submodule

/-! # 剰余体での互いに素な分解が定める平坦な局所拡大

## 概要

局所環 A 上の多項式 f の剰余体での還元が、既約な g と g に互いに素な h で f̄ = g·h と分解するとき、g が定める閉点で `AdjoinRoot f` を局所化した環 `ResidueFactorLocalRing f g h hf` を作る。この環の閉ファイバーは体 `AdjoinRoot g` であり、したがって極大イデアルは A の極大イデアルで生成される。`AdjoinRoot f` が A 上平坦（f がモニックならそう）なら、これは A 上平坦な局所拡大で、A がネーターなら次元が等しく、A が正則なら正則である。三次円分の場合 `CubicCyclotomicLocalRing` は、その根 ζ が ζ² + ζ + 1 = 0 を満たし、剰余体で 2 = 0 なら 3 が単元になる局所拡大を与える。

## 方針

閉ファイバー `AdjoinRoot f ⧸ m·AdjoinRoot f` を `AdjoinRoot.quotEquivQuotMap` で `AdjoinRoot (g·h)` と同一視する。g での局所化では余因子 h が可逆になるので g = 0 となり、局所化は `AdjoinRoot g` と同型である（`coprimeFactorLocalizationEquiv`）。全射な商と局所化の交換（`isLocalization_localizedSurjectiveQuotient`）で、これを局所環の閉ファイバーへ移す。次元と正則性は、極大イデアルを保つ平坦局所拡大の保存則（RegularLocalRing/FlatBaseChange）による。

## 規約

`adjoinRoot_map_mk`・`adjoinRoot_map_surjective` は Mathlib への提出候補。三次円分の局所環は剰余体での分解 `cubicCyclotomicPolynomial (ResidueField R) = g * h` を引数に取り、`cubicCyclotomicPolynomial_map_residue_eq` で一般論の仮定に直す。一般論の補題は三次円分の局所環にもそのまま使う。

## 使われ方

IntersectionMultiplicity/CubicCyclotomicBaseChange・AdamsVanishingThree（剰余標数 2 で 1 の原始三乗根を持つ正則局所環へ移る基底変換）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity
open Polynomial

section AdjoinRootMap

lemma adjoinRoot_map_mk {A : Type u} {K : Type v} [CommRing A] [CommRing K]
    (φ : A →+* K) (f : A[X]) (g : K[X]) (hdvd : g ∣ f.map φ) (q : A[X]) :
    AdjoinRoot.map φ f g hdvd (AdjoinRoot.mk f q) = AdjoinRoot.mk g (q.map φ) := by
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  exact AdjoinRoot.aeval_eq (q.map φ)

lemma adjoinRoot_map_surjective {A : Type u} {K : Type v} [CommRing A] [CommRing K]
    (φ : A →+* K) (hφ : Function.Surjective φ) (f : A[X]) (g : K[X])
    (hdvd : g ∣ f.map φ) : Function.Surjective (AdjoinRoot.map φ f g hdvd) := by
  intro x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective φ hφ q
  exact ⟨AdjoinRoot.mk f p, adjoinRoot_map_mk φ f g hdvd p⟩

end AdjoinRootMap

section CoprimeFactor

open Polynomial
variable {K : Type u} [Field K] (g h : K[X]) [Fact (Irreducible g)]

/-- The factor quotient map out of the product quotient. -/
def adjoinRootFactorMap : AdjoinRoot (g * h) →+* AdjoinRoot g :=
  AdjoinRoot.map (RingHom.id K) (g * h) g (by simp)

def adjoinRootFactorIdeal : Ideal (AdjoinRoot (g * h)) :=
  RingHom.ker (adjoinRootFactorMap g h)

instance adjoinRootFactorIdeal_isMaximal : (adjoinRootFactorIdeal g h).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (adjoinRoot_map_surjective (RingHom.id K) Function.surjective_id _ _ _)

lemma adjoinRootFactorMap_mk (q : K[X]) :
    adjoinRootFactorMap g h (AdjoinRoot.mk (g * h) q) = AdjoinRoot.mk g q := by
  simpa only [adjoinRootFactorMap, Polynomial.map_id] using
    adjoinRoot_map_mk (RingHom.id K) (g * h) g _ q

lemma cofactor_mem_primeCompl (hc : IsCoprime g h) :
    AdjoinRoot.mk (g * h) h ∈ (adjoinRootFactorIdeal g h).primeCompl := by
  have hu := hc.map (AdjoinRoot.mk g)
  rw [AdjoinRoot.mk_self, isCoprime_zero_left] at hu
  change adjoinRootFactorMap g h (AdjoinRoot.mk (g * h) h) ≠ 0
  rw [adjoinRootFactorMap_mk]
  exact hu.ne_zero

variable (T : Type u) [CommRing T] [Algebra (AdjoinRoot (g * h)) T]
    [IsLocalization (adjoinRootFactorIdeal g h).primeCompl T]

/-- The cofactor is inverted at the factor point, so the factor itself vanishes. -/
lemma factor_eq_zero_in_localization (hc : IsCoprime g h) :
    algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) g) = 0 := by
  have hu : IsUnit (algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) h)) :=
    IsLocalization.map_units T ⟨_, cofactor_mem_primeCompl g h hc⟩
  have hz : algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) g) *
      algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) h) = 0 := by
    rw [← map_mul, ← map_mul, AdjoinRoot.mk_self, map_zero]
  apply hu.mul_right_cancel
  simpa only [zero_mul] using hz

lemma factorRoot_relation (hc : IsCoprime g h) :
    g.eval₂ ((algebraMap (AdjoinRoot (g * h)) T).comp (AdjoinRoot.of (g * h)))
      (algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.root (g * h))) = 0 := by
  rw [← hom_eval₂, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
  exact factor_eq_zero_in_localization g h T hc

/-- The factor quotient maps back to the localization because the factor has become zero. -/
def factorLocalizationInverse (hc : IsCoprime g h) : AdjoinRoot g →+* T :=
  AdjoinRoot.lift ((algebraMap (AdjoinRoot (g * h)) T).comp (AdjoinRoot.of (g * h)))
    (algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.root (g * h)))
    (factorRoot_relation g h T hc)

lemma factorLocalizationInverse_comp (hc : IsCoprime g h) :
    (factorLocalizationInverse g h T hc).comp (adjoinRootFactorMap g h) =
      algebraMap (AdjoinRoot (g * h)) T := by
  ext r <;> simp [factorLocalizationInverse, adjoinRootFactorMap]

/-- Nonzero images of denominators give the forward localization map to the factor field. -/
def factorLocalizationMap : T →+* AdjoinRoot g :=
  IsLocalization.lift (M := (adjoinRootFactorIdeal g h).primeCompl)
    (fun s => (show adjoinRootFactorMap g h s ≠ 0 from s.property).isUnit)

lemma factorLocalizationMap_comp :
    (factorLocalizationMap g h T).comp (algebraMap (AdjoinRoot (g * h)) T) =
      adjoinRootFactorMap g h := IsLocalization.lift_comp _

lemma factorLocalizationMap_inverse_comp (hc : IsCoprime g h) :
    (factorLocalizationMap g h T).comp (factorLocalizationInverse g h T hc) =
      RingHom.id (AdjoinRoot g) := by
  ext r <;> simp [factorLocalizationInverse, factorLocalizationMap,
    IsLocalization.lift_eq, adjoinRootFactorMap]

/-- The localized product quotient is canonically the irreducible factor field. -/
def coprimeFactorLocalizationEquiv (hc : IsCoprime g h) : T ≃+* AdjoinRoot g := by
  refine RingEquiv.ofRingHom (factorLocalizationMap g h T)
    (factorLocalizationInverse g h T hc) ?_ ?_
  · exact factorLocalizationMap_inverse_comp g h T hc
  · apply IsLocalization.ringHom_ext (adjoinRootFactorIdeal g h).primeCompl
    rw [RingHom.comp_assoc, factorLocalizationMap_comp, factorLocalizationInverse_comp]
    rfl

lemma isField_coprimeFactorLocalization (hc : IsCoprime g h) : IsField T :=
  (coprimeFactorLocalizationEquiv g h T hc).toMulEquiv.isField
    (inferInstance : Field (AdjoinRoot g)).toIsField


end CoprimeFactor

section LocalizedSurjectiveQuotient

variable {C : Type u} {D : Type v} [CommRing C] [CommRing D]
    (π : C →+* D) (hπ : Function.Surjective π)
    (B : Type w) [CommRing B] [Algebra C B]

/-- The quotient of a C-algebra by the extended kernel is a D-algebra. -/
@[instance_reducible]
def localizedSurjectiveQuotientAlgebra :
    Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
  ((algebraMap (C ⧸ RingHom.ker π) (B ⧸ (RingHom.ker π).map (algebraMap C B))).comp
    (π.quotientKerEquivOfSurjective hπ).symm.toRingHom).toAlgebra

lemma localizedSurjectiveQuotientAlgebra_commutes (x : C) :
    let : Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
      localizedSurjectiveQuotientAlgebra π hπ B
    algebraMap D (B ⧸ (RingHom.ker π).map (algebraMap C B)) (π x) =
      Ideal.Quotient.mk _ (algebraMap C B x) := by
  change algebraMap (C ⧸ RingHom.ker π) _
    ((π.quotientKerEquivOfSurjective hπ).symm (π x)) = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

/-- The quotient of the localization localizes the target at the original prime. -/
lemma isLocalization_localizedSurjectiveQuotient (q : Ideal D) [q.IsPrime]
    [IsLocalization (q.comap π).primeCompl B] :
    let : Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
      localizedSurjectiveQuotientAlgebra π hπ B
    IsLocalization q.primeCompl (B ⧸ (RingHom.ker π).map (algebraMap C B)) := by
  let : Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
    localizedSurjectiveQuotientAlgebra π hπ B
  have hl : IsLocalization ((q.comap π).primeCompl.map π)
      (B ⧸ (RingHom.ker π).map (algebraMap C B)) := by
    apply IsLocalization.of_surjective (q.comap π).primeCompl B π hπ
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    · ext x
      exact (localizedSurjectiveQuotientAlgebra_commutes π hπ B x).symm
    · rw [Ideal.mk_ker]
  rw [Ideal.map_primeCompl_comap_of_surjective π hπ q] at hl
  exact hl


end LocalizedSurjectiveQuotient

section ResidueFactor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open IsLocalRing
variable {R : Type u} [CommRing R] [IsLocalRing R] (f : R[X])
    (g h : (ResidueField R)[X]) (hf : f.map (residue R) = g * h)

/-- 閉ファイバーへの写像を、選んだ分解の座標で書いたもの。 -/
def residueFactorFiberMap : AdjoinRoot f →+* AdjoinRoot (g * h) :=
  AdjoinRoot.map (residue R) f (g * h) (by rw [hf])

lemma residueFactorFiberMap_surjective : Function.Surjective (residueFactorFiberMap f g h hf) :=
  adjoinRoot_map_surjective _ residue_surjective _ _ _

/-- 多項式の商の基底変換の比較を、分解を固定して書いたもの。 -/
def residueFactorClosedFiberEquiv :
    (AdjoinRoot f ⧸ (maximalIdeal R).map (algebraMap R (AdjoinRoot f))) ≃+*
      AdjoinRoot (g * h) :=
  (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)).toRingEquiv.trans
    (Ideal.quotEquivOfEq (by
      change Ideal.span ({f.map (residue R)} : Set (ResidueField R)[X]) = Ideal.span {g * h}
      rw [hf]))

lemma residueFactorClosedFiberEquiv_comp :
    (residueFactorClosedFiberEquiv f g h hf).toRingHom.comp (Ideal.Quotient.mk _) =
      residueFactorFiberMap f g h hf := by
  apply RingHom.ext
  intro x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  change residueFactorClosedFiberEquiv f g h hf (Ideal.Quotient.mk _ (AdjoinRoot.mk f q)) = _
  have he := AdjoinRoot.quotEquivQuotMap_apply_mk f q (maximalIdeal R)
  have he' := congrArg (Ideal.quotEquivOfEq (show
    Ideal.span ({f.map (residue R)} : Set (ResidueField R)[X]) = Ideal.span {g * h} by
      rw [hf])) he
  have he'' : residueFactorClosedFiberEquiv f g h hf (Ideal.Quotient.mk _ (AdjoinRoot.mk f q)) =
      AdjoinRoot.mk (g * h) (q.map (residue R)) := by
    exact he'.trans (Ideal.quotEquivOfEq_mk _ _)
  exact he''.trans (adjoinRoot_map_mk (residue R) f (g * h) _ q).symm

lemma residueFactorFiberMap_ker :
    RingHom.ker (residueFactorFiberMap f g h hf) =
      (maximalIdeal R).map (algebraMap R (AdjoinRoot f)) := by
  rw [← residueFactorClosedFiberEquiv_comp]
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply]
  rw [map_eq_zero_iff (residueFactorClosedFiberEquiv f g h hf).toRingHom
      (residueFactorClosedFiberEquiv f g h hf).injective,
    Ideal.Quotient.eq_zero_iff_mem]

variable [Fact (Irreducible g)]

/-- 選んだ因子の点を、閉ファイバー上の点の引き戻しとして書いたもの。 -/
def residueFactorPoint : Ideal (AdjoinRoot f) :=
  (adjoinRootFactorIdeal g h).comap (residueFactorFiberMap f g h hf)

instance residueFactorPoint_isMaximal : (residueFactorPoint f g h hf).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective (residueFactorFiberMap f g h hf)
    (residueFactorFiberMap_surjective f g h hf)

lemma residueFactorPoint_comap :
    (residueFactorPoint f g h hf).comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R := by
  ext r
  change adjoinRootFactorMap g h (residueFactorFiberMap f g h hf (AdjoinRoot.of f r)) = 0 ↔
    r ∈ maximalIdeal R
  simp only [residueFactorFiberMap, AdjoinRoot.map_of, adjoinRootFactorMap, RingHom.id_apply]
  rw [map_eq_zero_iff (AdjoinRoot.of g) (AdjoinRoot.of g).injective, residue_eq_zero_iff]

section LocalFiber

variable (B : Type u) [CommRing B] [Algebra (AdjoinRoot f) B]
    [Algebra R B] [IsScalarTower R (AdjoinRoot f) B]
    [hB : IsLocalization (residueFactorPoint f g h hf).primeCompl B]

include hB

/-- 選んだ点での局所的な閉ファイバーは、既約因子の体である。 -/
lemma residueFactor_localFiber_isField (hc : IsCoprime g h) :
    IsField (B ⧸ (maximalIdeal R).map (algebraMap R B)) := by
  let π := residueFactorFiberMap f g h hf
  have hp : Function.Surjective π := residueFactorFiberMap_surjective f g h hf
  let T := B ⧸ (RingHom.ker π).map (algebraMap (AdjoinRoot f) B)
  let : IsLocalization ((adjoinRootFactorIdeal g h).comap π).primeCompl B := hB
  let : Algebra (AdjoinRoot (g * h)) T := localizedSurjectiveQuotientAlgebra π hp B
  let : IsLocalization (adjoinRootFactorIdeal g h).primeCompl T :=
    isLocalization_localizedSurjectiveQuotient π hp B (adjoinRootFactorIdeal g h)
  have hfield : IsField T := isField_coprimeFactorLocalization g h T hc
  have hm : (RingHom.ker π).map (algebraMap (AdjoinRoot f) B) =
      (maximalIdeal R).map (algebraMap R B) := by
    rw [residueFactorFiberMap_ker, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (AdjoinRoot f) B]
  change IsField (B ⧸ (RingHom.ker π).map (algebraMap (AdjoinRoot f) B)) at hfield
  rw [hm] at hfield
  exact hfield

/-- 閉ファイバーが体なので、拡大した極大イデアルは極大イデアルである。 -/
lemma residueFactor_local_map_maximalIdeal [IsLocalRing B] (hc : IsCoprime g h) :
    (maximalIdeal R).map (algebraMap R B) = maximalIdeal B := by
  have hi := Ideal.Quotient.maximal_of_isField ((maximalIdeal R).map (algebraMap R B))
    (residueFactor_localFiber_isField f g h hf B hc)
  exact eq_maximalIdeal hi

end LocalFiber

/-- 選んだ因子の点での局所拡大。 -/
abbrev ResidueFactorLocalRing := Localization.AtPrime (residueFactorPoint f g h hf)

instance residueFactorLocalRing_algebra : Algebra R (ResidueFactorLocalRing f g h hf) :=
  ((algebraMap (AdjoinRoot f) (ResidueFactorLocalRing f g h hf)).comp
    (algebraMap R (AdjoinRoot f))).toAlgebra

-- 塔を合成するときのスカラー作用を、構造写像の代数のものに固定する。
local instance residueFactorSourceSMul : SMul R (AdjoinRoot f) :=
  (inferInstance : Algebra R (AdjoinRoot f)).toSMul
local instance residueFactorTargetSMul :
    SMul (AdjoinRoot f) (ResidueFactorLocalRing f g h hf) :=
  (inferInstance : Algebra (AdjoinRoot f) (ResidueFactorLocalRing f g h hf)).toSMul
local instance residueFactorBaseSMul : SMul R (ResidueFactorLocalRing f g h hf) :=
  (inferInstance : Algebra R (ResidueFactorLocalRing f g h hf)).toSMul

instance residueFactorLocalRing_scalarTower :
    IsScalarTower R (AdjoinRoot f) (ResidueFactorLocalRing f g h hf) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := AdjoinRoot f)
    (A := ResidueFactorLocalRing f g h hf) rfl

instance residueFactorLocalRing_noetherian [IsNoetherianRing R] :
    IsNoetherianRing (ResidueFactorLocalRing f g h hf) :=
  IsLocalization.isNoetherianRing (residueFactorPoint f g h hf).primeCompl _ inferInstance

local instance residueFactorBaseModule : Module R (ResidueFactorLocalRing f g h hf) :=
  Algebra.toModule

instance residueFactorLocalRing_flat [Module.Flat R (AdjoinRoot f)] :
    Module.Flat R (ResidueFactorLocalRing f g h hf) := by
  let : Module.Flat (AdjoinRoot f) (ResidueFactorLocalRing f g h hf) :=
    IsLocalization.flat _ (residueFactorPoint f g h hf).primeCompl
  exact Module.Flat.trans R (AdjoinRoot f) (ResidueFactorLocalRing f g h hf)

lemma residueFactorLocalRing_map_maximalIdeal (hc : IsCoprime g h) :
    (maximalIdeal R).map (algebraMap R (ResidueFactorLocalRing f g h hf)) =
      maximalIdeal (ResidueFactorLocalRing f g h hf) :=
  residueFactor_local_map_maximalIdeal f g h hf _ hc

lemma residueFactorLocalRing_dimension [IsNoetherianRing R] [Module.Flat R (AdjoinRoot f)]
    (hc : IsCoprime g h) :
    ringKrullDim (ResidueFactorLocalRing f g h hf) = ringKrullDim R :=
  ringKrullDim_eq_of_flat_of_map_maximalIdeal R _
    (residueFactorLocalRing_map_maximalIdeal f g h hf hc)

-- 選んだ剰余因子と局所環は、元の局所環の添字のまま扱う。
set_option linter.overlappingInstances false in
lemma residueFactorLocalRing_regular [IsRegularLocalRing R] [Module.Flat R (AdjoinRoot f)]
    (hc : IsCoprime g h) :
    IsRegularLocalRing (ResidueFactorLocalRing f g h hf) :=
  isRegularLocalRing_of_flat_of_map_maximalIdeal R _
    (residueFactorLocalRing_map_maximalIdeal f g h hf hc)

end ResidueFactor

section CubicCyclotomicLocal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open IsLocalRing
variable {R : Type u} [CommRing R] [IsLocalRing R]
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)

include hf in
/-- 剰余体での三次円分多項式の分解を、R 上の多項式の還元の分解として読む。 -/
lemma cubicCyclotomicPolynomial_map_residue_eq :
    (cubicCyclotomicPolynomial R).map (residue R) = g * h :=
  (map_cyclotomic 3 (residue R)).trans hf

variable [Fact (Irreducible g)]

/-- 剰余体での X² + X + 1 の既約因子が定める点での局所拡大。 -/
abbrev CubicCyclotomicLocalRing :=
  ResidueFactorLocalRing (cubicCyclotomicPolynomial R) g h
    (cubicCyclotomicPolynomial_map_residue_eq g h hf)

/-- 局所拡大の中の 1 の原始三乗根。 -/
def cubicCyclotomicLocalRoot : CubicCyclotomicLocalRing g h hf :=
  algebraMap (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf) (cubicCyclotomicRoot R)

lemma cubicCyclotomicLocalRoot_relation :
    cubicCyclotomicLocalRoot g h hf ^ 2 + cubicCyclotomicLocalRoot g h hf + 1 = 0 := by
  have he := congrArg (algebraMap (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf))
    (cubicCyclotomicRoot_relation R)
  rw [map_add, map_add, map_pow, map_one, map_zero] at he
  exact he

lemma cubicCyclotomicLocalRing_three_isUnit (htwo : (2 : ResidueField R) = 0) :
    IsUnit (3 : CubicCyclotomicLocalRing g h hf) := by
  simpa only [map_ofNat] using (isUnit_three_of_residue_two_eq_zero htwo).map
    (algebraMap R (CubicCyclotomicLocalRing g h hf))

end CubicCyclotomicLocal

end SerrePositivity
