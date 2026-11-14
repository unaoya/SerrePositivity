module


public meta import SerrePositivity.Util.Citation
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModuleComplete

import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
import all SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
import all SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty
public import Mathlib.LinearAlgebra.TensorProduct.Lift

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateGradedDGAlgebra
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneSquare
public import SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateGradedDGAlgebra
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyCupGradedRing
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz

/-!
# 未完備多項式形式からの Hodge–Tate 写像

## 概要
完備化単位を通した η⁰・η¹ を、多項式 de Rham 代数の普遍性で高次に延ばす。

## 方針
係数の作用を cup 積と照合し、一次の平方零と微分公式を普遍性へ渡す。

## 規約
多項式の変数を係数環の宇宙へ持ち上げる。

## 使われ方
完備多項式形式への延長。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
  SerrePositivity.DerivedCompletion
open scoped DirectSum TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
  (hP : IsBoundedPrism P) (r : ℕ)

private abbrev rawFormVars (_A : Type u) (r : ℕ) : Type u := formVars r
local notation "k" => A ⧸ P.ideal
local notation "T" => rawFormVars A r
local notation "B" => Poly k T
local notation "Q" => completedPoly k T p
local notation "R" => affineAlgebra P r
local notation "S" => htGradedDGAlgebra P hP r
local notation "H" => hodgeTateCohomology' P hP r
local notation "X" => reducedModel P hP r

local instance (i : ℕ) : Module R (H i) := htModule P hP r i

private def rawCoefficient : B →+* R :=
  (affineCoordinateIso P r).symm.toRingHom.comp (algebraMap B Q)

set_option backward.isDefEq.respectTransparency false in
private def etaZeroRaw : B →+* (S).carrier 0 where
  toFun f := hodgeTateMapZero P hP r (rawCoefficient P r f)
  map_zero' := by rw [map_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_add' x y := by rw [map_add, map_add]
  map_mul' x y := by
    change hodgeTateMapZero P hP r (rawCoefficient P r (x*y)) =
      cohomologyCup X (hodgeTateMapZero P hP r (rawCoefficient P r x))
        (hodgeTateMapZero P hP r (rawCoefficient P r y))
    rw [map_mul, etaZero_mul]

private def etaOneRaw : forms k T 1 →+ (S).carrier 1 :=
  (hodgeTateMapOne P hP r).toAddMonoidHom.comp (completedFormsUnit k T p 1)

private theorem completedFormsUnit_smul_raw (i : ℕ) (f : B) (w : forms k T i) :
    completedFormsUnit k T p i (f • w) = rawCoefficient P r f • completedFormsUnit k T p i w := by
  let : Algebra B Q := completedPolyAlgebra k T p
  change (1 : Q) ⊗ₜ[B] (f • w) =
    affineCoordinateIso P r (rawCoefficient P r f) • ((1 : Q) ⊗ₜ[B] w)
  change _ = affineCoordinateIso P r ((affineCoordinateIso P r).symm (algebraMap B Q f)) • _
  rw [RingEquiv.apply_symm_apply, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  rw [Algebra.smul_def f (1 : Q), mul_one]
  rw [smul_eq_mul, mul_one]

private theorem degreeZeroForm_unit_raw (f : B) :
    degreeZeroForm P r (rawCoefficient P r f) =
      completedFormsUnit k T p 0 (formsZeroEquiv k T f) := by
  let : Algebra B Q := completedPolyAlgebra k T p
  change completeZeroForm P r
    (affineCoordinateIso P r ((affineCoordinateIso P r).symm (algebraMap B Q f))) = _
  rw [RingEquiv.apply_symm_apply]
  simp only [completeZeroForm, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.rid_symm_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply]
  change (algebraMap B Q f) ⊗ₜ[B] (polynomialZeroForm P r 1) =
    (1 : Q) ⊗ₜ[B] (polynomialZeroForm P r f)
  have h : polynomialZeroForm P r f = f • polynomialZeroForm P r 1 := by
    have hs := (polynomialZeroForm P r).map_smul f (1 : B)
    simpa only [smul_eq_mul, mul_one, RingHom.id_apply] using hs
  rw [h, ← TensorProduct.smul_tmul]
  rw [Algebra.smul_def f (1 : Q), mul_one]

private theorem etaRaw_smul (f : B) (w : forms k T 1) :
    etaOneRaw P hP r (f • w) = etaZeroRaw P hP r f • etaOneRaw P hP r w := by
  let v := hodgeTateMapOne P hP r (completedFormsUnit k T p 1 w)
  let a := rawCoefficient P r f
  have hv : a • v = cohomologyCup X (hodgeTateMapZero P hP r a) v :=
    (htModuleData P hP r 1).property a v
  change hodgeTateMapOne P hP r (completedFormsUnit k T p 1 (f • w)) =
    etaZeroRaw P hP r f • (show (S).carrier 1 from v)
  rw [completedFormsUnit_smul_raw, map_smul, hv]
  apply DirectSum.of_injective (β := (S).carrier) 1
  rw [DirectSum.of_zero_smul, DirectSum.of_mul_of]
  rfl

private theorem etaRaw_d (f : B) :
    etaOneRaw P hP r (deRhamD k T 0 (formsZeroEquiv k T f)) =
      (S).d 0 (etaZeroRaw P hP r f) := by
  change hodgeTateMapOne P hP r
      (completedFormsUnit k T p 1 (deRhamD k T 0 (formsZeroEquiv k T f))) =
    htBocksteinZero P hP r (rawCoefficient P r f)
  rw [← completedDeRhamD_unit, ← degreeZeroForm_unit_raw]
  exact htOneOnGenerators_d P hP r _

/-- 未完備多項式 de Rham 形式上の Hodge–Tate 写像とその普遍性。 -/
private theorem existsUnique_rawHodgeTate :
    ∃! Φ : ∀ i, forms k T i →+ (S).carrier i,
      (∀ f, Φ 0 (formsZeroEquiv k T f) = etaZeroRaw P hP r f) ∧
      (∀ ω, Φ 1 ω = etaOneRaw P hP r ω) ∧
      (∀ {i j} (ω : forms k T i) (η : forms k T j),
        Φ (i+j) (wedge k T ω η) = (S).mul (Φ i ω) (Φ j η)) ∧
      (∀ i ω, Φ (i+1) (deRhamD k T i ω) = (S).d i (Φ i ω)) :=
  exists_unique_dgHom k T (S) (etaZeroRaw P hP r) (etaOneRaw P hP r)
    (etaRaw_smul P hP r) (etaRaw_d P hP r)
    (fun w => hodgeTateMapOne_square_zero P hP r (completedFormsUnit k T p 1 w))

open CategoryTheory

private def rawHodgeTate (i : ℕ) : forms k T i →+ (S).carrier i :=
  (existsUnique_rawHodgeTate P hP r).exists.choose i

private theorem rawHodgeTate_zero (f : B) :
    rawHodgeTate P hP r 0 (formsZeroEquiv k T f) = etaZeroRaw P hP r f :=
  (existsUnique_rawHodgeTate P hP r).exists.choose_spec.1 f

private theorem rawHodgeTate_mul {i j : ℕ} (x : forms k T i) (y : forms k T j) :
    rawHodgeTate P hP r (i+j) (wedge k T x y) =
      (S).mul (rawHodgeTate P hP r i x) (rawHodgeTate P hP r j y) :=
  (existsUnique_rawHodgeTate P hP r).exists.choose_spec.2.2.1 x y

private theorem rawHodgeTate_d (i : ℕ) (x : forms k T i) :
    rawHodgeTate P hP r (i+1) (deRhamD k T i x) =
      (S).d i (rawHodgeTate P hP r i x) :=
  (existsUnique_rawHodgeTate P hP r).exists.choose_spec.2.2.2 i x

private theorem formsZero_wedge (i : ℕ) (f : B) (ω : forms k T i) :
    cast (congrArg (fun n => forms k T n) (Nat.zero_add i))
      (wedge k T (formsZeroEquiv k T f) ω) = f • ω := by
  induction ω using TensorProduct.inductionOn with
  | add x y hx hy =>
    have hAdd {j l : ℕ} (h : j = l) (x y : forms k T j) :
        cast (congrArg (fun n => forms k T n) h) (x+y) =
          cast (congrArg (fun n => forms k T n) h) x +
            cast (congrArg (fun n => forms k T n) h) y := by
      subst l
      rfl
    change cast (congrArg (fun n => forms k T n) (Nat.zero_add i))
      ((TensorProduct.map₂ (LinearMap.mul k B) (exteriorWedge k (T → k) 0 i))
        (formsZeroEquiv k T f) (x+y)) = f • (x+y)
    erw [map_add, hAdd (Nat.zero_add i), smul_add, hx, hy]
  | tmul g v =>
    have h : cast (congrArg (fun n => ↥(⋀[k]^n (T → k))) (Nat.zero_add i))
        (exteriorWedge k (T → k) 0 i ((exteriorPower.zeroEquiv k (T → k)).symm 1) v) = v := by
      have hc {j l : ℕ} (e : j = l) (a : ⋀[k]^j (T → k)) :
          (cast (congrArg (fun n => ↥(⋀[k]^n (T → k))) e) a).1 = a.1 := by
        subst l
        rfl
      apply Subtype.ext
      rw [hc (Nat.zero_add i)]
      change ((exteriorPower.zeroEquiv k (T → k)).symm 1).1 * v.1 = v.1
      simp [exteriorPower.zeroEquiv, ExteriorAlgebra.ιMulti_apply]
    rw [formsZeroEquiv_tmul, wedge_tmul, cast_tmul (Nat.zero_add i), h]
    rfl

set_option maxHeartbeats 1200000 in
-- cup 積と完備係数の作用を次数の変換込みで照合する。
set_option backward.isDefEq.respectTransparency false in
private theorem rawHodgeTate_smul (i : ℕ) (f : B) (ω : forms k T i) :
    rawHodgeTate P hP r i (f • ω) =
      rawCoefficient P r f • (show H i from rawHodgeTate P hP r i ω) := by
  have hc {a b : ℕ} (h : a = b) (w : forms k T a) :
      rawHodgeTate P hP r b (cast (congrArg (fun n => forms k T n) h) w) =
        cast (congrArg (H) h) (rawHodgeTate P hP r a w) := by
    subst b
    rfl
  let v : H i := rawHodgeTate P hP r i ω
  let a := rawCoefficient P r f
  have hs := (htModuleData P hP r i).property a v
  change a • v = cast (congrArg (H) (Nat.zero_add i))
    (cohomologyCup X (hodgeTateMapZero P hP r a) v) at hs
  erw [← formsZero_wedge P r i f ω, hc (Nat.zero_add i), rawHodgeTate_mul, rawHodgeTate_zero]
  exact hs.symm

@[instance_reducible] private def htRawQModule (i : ℕ) : Module Q (H i) :=
  Module.compHom _ (affineCoordinateIso P r).symm.toRingHom

attribute [local instance] htRawQModule

@[instance_reducible] private def htRawPolynomialModule (i : ℕ) : Module B (H i) :=
  Module.compHom _ (rawCoefficient P r)

attribute [local instance] htRawPolynomialModule

private theorem htRawScalarTower (i : ℕ) : IsScalarTower B Q (H i) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] htRawScalarTower

private def rawHodgeTateLinear (i : ℕ) : forms k T i →ₗ[B] H i where
  toFun := rawHodgeTate P hP r i
  map_add' := map_add _
  map_smul' f ω := rawHodgeTate_smul P hP r i f ω

private def completedHodgeTateLinear (i : ℕ) : affineForms P r i →ₗ[Q] H i :=
  (rawHodgeTateLinear P hP r i).liftBaseChange Q

private theorem completedHodgeTateLinear_unit (i : ℕ) (ω : forms k T i) :
    completedHodgeTateLinear P hP r i (completedFormsUnit k T p i ω) =
      rawHodgeTate P hP r i ω :=
  (rawHodgeTateLinear P hP r i).liftBaseChange_one_tmul Q ω

/-- 完備多項式形式から affine Hodge–Tate コホモロジーへの写像。 -/
def completedHodgeTate (i : ℕ) : affineForms P r i →ₗ[R] H i where
  toFun := completedHodgeTateLinear P hP r i
  map_add' := map_add _
  map_smul' f ω := by
    change completedHodgeTateLinear P hP r i (affineCoordinateIso P r f • ω) =
      f • completedHodgeTateLinear P hP r i ω
    rw [map_smul]
    have he : (affineCoordinateIso P r f) •
        (completedHodgeTateLinear P hP r i ω) =
        (affineCoordinateIso P r).symm (affineCoordinateIso P r f) •
          (completedHodgeTateLinear P hP r i ω) := rfl
    rw [he, RingEquiv.symm_apply_apply]

private theorem completedHodgeTate_unit (i : ℕ) (ω : forms k T i) :
    completedHodgeTate P hP r i (completedFormsUnit k T p i ω) =
      rawHodgeTate P hP r i ω :=
  completedHodgeTateLinear_unit P hP r i ω

/-- 完備多項式形式の写像は次数零で η⁰ に一致する。 -/
theorem completedHodgeTate_zero (f : R) :
    completedHodgeTate P hP r 0 (degreeZeroForm P r f) = hodgeTateMapZero P hP r f := by
  have he : degreeZeroForm P r f = f • degreeZeroForm P r 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hz : degreeZeroForm P r 1 = completedFormsUnit k T p 0 (formsZeroEquiv k T 1) := by
    rw [← map_one (rawCoefficient P r), degreeZeroForm_unit_raw]
  rw [he, hz, map_smul, completedHodgeTate_unit, rawHodgeTate_zero]
  have h := (htModuleData P hP r 0).property f (hodgeTateMapZero P hP r 1)
  change f • (hodgeTateMapZero P hP r 1) =
    cohomologyCup X (hodgeTateMapZero P hP r f) (hodgeTateMapZero P hP r 1) at h
  change f • (hodgeTateMapZero P hP r (rawCoefficient P r 1)) = _
  rw [map_one (rawCoefficient P r), h, map_one, cohomologyCup_one_right]

private def etaOneQ : affineForms P r 1 →ₗ[Q] H 1 where
  toFun := hodgeTateMapOne P hP r
  map_add' := map_add _
  map_smul' f ω := by
    have h : (affineCoordinateIso P r).symm f • ω = f • ω := by
      change affineCoordinateIso P r ((affineCoordinateIso P r).symm f) • ω = f • ω
      rw [RingEquiv.apply_symm_apply]
    rw [← h, map_smul]
    rfl

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- 完備多項式形式の写像は次数一で η¹ に一致する。 -/
theorem completedHodgeTate_one :
    completedHodgeTate P hP r 1 = hodgeTateMapOne P hP r := by
  suffices completedHodgeTateLinear P hP r 1 = etaOneQ P hP r by
    ext ω
    exact DFunLike.congr_fun this ω
  let e : (forms k T 1 →ₗ[B] H 1) ≃ (affineForms P r 1 →ₗ[Q] H 1) :=
    (LinearMap.liftBaseChangeEquiv Q).toEquiv
  apply e.symm.injective
  apply LinearMap.ext
  intro ω
  change completedHodgeTateLinear P hP r 1 (completedFormsUnit k T p 1 ω) =
    hodgeTateMapOne P hP r (completedFormsUnit k T p 1 ω)
  rw [completedHodgeTateLinear_unit]
  exact (existsUnique_rawHodgeTate P hP r).exists.choose_spec.2.1 ω

local instance d68TargetBaseModule (i : ℕ) : Module k (H i) :=
  Module.compHom _ (algebraMap k R)

local instance d68TargetTower (i : ℕ) : IsScalarTower k R (H i) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private theorem htBaseComplete (i : ℕ) :
    IsModuleComplete k (p : k) (ModuleCat.of k (H i)) :=
  (isModuleComplete_algebraMap_iff k R (p : k) (H i)).mp (by
    rw [map_natCast]
    exact htModule_isModuleComplete P hP r i)

private def completedEtaBase (i : ℕ) : affineForms P r i →ₗ[k] H i where
  toFun := completedHodgeTate P hP r i
  map_add' := map_add _
  map_smul' a x := by
    have he : (algebraMap k R a) • x = a • x := by
      change affineCoordinateIso P r (algebraMap k R a) • x = _
      rw [coord_map_C P r]
      exact algebraMap_smul Q a x
    change completedHodgeTate P hP r i (a • x) =
      (algebraMap k R a) • completedHodgeTate P hP r i x
    rw [← he, map_smul]

set_option backward.isDefEq.respectTransparency false in
private def htCupLinear (i j : ℕ) : H i →ₗ[k] H j →ₗ[k] H (i+j) := by
  let G := htGradedDGAlgebra P hP r
  let J := DirectSum.of G.carrier
  let f : G.carrier i →ₗ[k] G.carrier j →ₗ[k] G.carrier (i+j) :=
    LinearMap.mk₂ k G.mul
      (fun x y z => (cohomologyCupGradedRing X).add_mul x y z)
      (fun a x y => by
        apply DirectSum.of_injective (β := G.carrier) (i+j)
        change J (i+j) (GradedMonoid.GMul.mul (a • x) y) =
          J (i+j) (a • GradedMonoid.GMul.mul x y)
        rw [← DirectSum.of_mul_of (a • x) y, DirectSum.of_smul, smul_mul_assoc, DirectSum.of_mul_of,
          DirectSum.of_smul])
      (fun x y z => (cohomologyCupGradedRing X).mul_add x y z)
      (fun a x y => by
        apply DirectSum.of_injective (β := G.carrier) (i+j)
        change J (i+j) (GradedMonoid.GMul.mul x (a • y)) =
          J (i+j) (a • GradedMonoid.GMul.mul x y)
        rw [← DirectSum.of_mul_of x (a • y), DirectSum.of_smul, mul_smul_comm, DirectSum.of_mul_of,
          DirectSum.of_smul])
  exact f

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- 完備形式からの Hodge–Tate 写像は外積を cup 積に送る。 -/
theorem completedHodgeTate_mul {i j : ℕ} (x : affineForms P r i) (y : affineForms P r j) :
    completedHodgeTate P hP r (i+j) (affineWedge P r x y) =
      cohomologyCup X (completedHodgeTate P hP r i x) (completedHodgeTate P hP r j y) := by
  let e := completedEtaBase P hP r
  let u := completedFormsUnit k T p
  let l : affineForms P r i →ₗ[k] affineForms P r j →ₗ[k] H (i+j) :=
    (wedgeLinear k T p i j).compr₂ (e (i+j))
  let m : affineForms P r i →ₗ[k] affineForms P r j →ₗ[k] H (i+j) :=
    (htCupLinear P hP r i j).compl₁₂ (e i) (e j)
  have hunit (a : forms k T i) (b : forms k T j) : l (u i a) (u j b) = m (u i a) (u j b) := by
    change completedHodgeTate P hP r (i+j) (completedWedge k T p (u i a) (u j b)) =
      cohomologyCup X (completedHodgeTate P hP r i (u i a))
        (completedHodgeTate P hP r j (u j b))
    rw [completedWedge_unit, completedHodgeTate_unit, completedHodgeTate_unit,
      completedHodgeTate_unit, rawHodgeTate_mul]
    rfl
  have hleft (b : forms k T j) : l.flip (u j b) = m.flip (u j b) :=
    completedForms_linearMap_ext k T p (htBaseComplete P hP r (i+j)) fun a => hunit a b
  have hright : l x = m x :=
    completedForms_linearMap_ext k T p (htBaseComplete P hP r (i+j)) fun b =>
      LinearMap.congr_fun (hleft b) x
  exact LinearMap.congr_fun hright y

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- 完備形式からの Hodge–Tate 写像は de Rham 微分を Bockstein に送る。 -/
theorem completedHodgeTate_d (i : ℕ) (x : affineForms P r i) :
    completedHodgeTate P hP r (i+1) (affineD P r i x) =
      bockstein P hP r i (completedHodgeTate P hP r i x) := by
  let e := completedEtaBase P hP r
  let l := (e (i+1)).comp (dLinear k T p i)
  let m := (htBaseD P hP r i).comp (e i)
  have h : l = m := completedForms_linearMap_ext k T p (htBaseComplete P hP r (i+1)) (by
    intro a
    change completedHodgeTate P hP r (i+1)
      (completedDeRhamD k T p i (completedFormsUnit k T p i a)) =
        bockstein P hP r i (completedHodgeTate P hP r i (completedFormsUnit k T p i a))
    rw [completedDeRhamD_unit, completedHodgeTate_unit, completedHodgeTate_unit, rawHodgeTate_d]
    rfl)
  exact LinearMap.congr_fun h x

/-- 完備多項式 de Rham 形式からの乗法的 Hodge–Tate 写像。 -/
structure HTAlgebraMap where
  app (i : ℕ) : affineForms P r i →ₗ[affineAlgebra P r] hodgeTateCohomology' P hP r i
  on_zero (f) : app 0 (degreeZeroForm P r f) = hodgeTateMapZero P hP r f
  on_one : app 1 = hodgeTateMapOne P hP r
  product {i j} (x : affineForms P r i) (y : affineForms P r j) :
    app (i+j) (affineWedge P r x y) = cohomologyCup (reducedModel P hP r) (app i x) (app j y)
  differential (i) (x : affineForms P r i) :
    app (i+1) (affineD P r i x) = bockstein P hP r i (app i x)

/-- η⁰ と η¹ を完備形式の全次数へ延長する。 -/
def hodgeTateMap : HTAlgebraMap P hP r where
  app := completedHodgeTate P hP r
  on_zero := completedHodgeTate_zero P hP r
  on_one := completedHodgeTate_one P hP r
  product := completedHodgeTate_mul P hP r
  differential := completedHodgeTate_d P hP r

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- η⁰ と η¹ を延長する完備微分代数の写像は一意。 -/
theorem hodgeTateMap_unique (f : HTAlgebraMap P hP r) : f = hodgeTateMap P hP r := by
  let u := completedFormsUnit k T p
  let F (i : ℕ) : forms k T i →+ (S).carrier i := (f.app i).toAddMonoidHom.comp (u i)
  have hF : F = rawHodgeTate P hP r :=
    (existsUnique_rawHodgeTate P hP r).unique
      ⟨fun a => by
        change f.app 0 (u 0 (formsZeroEquiv k T a)) = _
        rw [← degreeZeroForm_unit_raw, f.on_zero]
        rfl,
      fun w => by
        change f.app 1 (u 1 w) = _
        rw [f.on_one]
        rfl,
      fun {i j} x y => by
        change f.app (i+j) (u (i+j) (wedge k T x y)) =
          cohomologyCup X (f.app i (u i x)) (f.app j (u j y))
        rw [← completedWedge_unit]
        exact f.product _ _,
      fun i w => by
        change f.app (i+1) (u (i+1) (deRhamD k T i w)) = bockstein P hP r i (f.app i (u i w))
        rw [← completedDeRhamD_unit]
        exact f.differential _ _⟩
      (existsUnique_rawHodgeTate P hP r).exists.choose_spec
  have happ : f.app = (hodgeTateMap P hP r).app := by
    funext i
    let g : affineForms P r i →ₗ[Q] H i :=
      { toFun := f.app i
        map_add' := map_add _
        map_smul' := fun c w => by
          have hc : (affineCoordinateIso P r).symm c • w = c • w := by
            change affineCoordinateIso P r ((affineCoordinateIso P r).symm c) • w = c • w
            rw [RingEquiv.apply_symm_apply]
          rw [← hc, map_smul]
          rfl }
    let e : (forms k T i →ₗ[B] H i) ≃ (affineForms P r i →ₗ[Q] H i) :=
      (LinearMap.liftBaseChangeEquiv Q).toEquiv
    have he : g = completedHodgeTateLinear P hP r i := by
      apply e.symm.injective
      apply LinearMap.ext
      intro w
      change f.app i (u i w) = completedHodgeTateLinear P hP r i (u i w)
      rw [completedHodgeTateLinear_unit]
      exact DFunLike.congr_fun (congrFun hF i) w
    apply LinearMap.ext
    intro w
    exact DFunLike.congr_fun he w
  cases f
  cases h : hodgeTateMap P hP r
  rw [h] at happ
  cases happ
  rfl

/-- 多項式 Hodge–Tate 比較が全次数で同型であるという述語。 -/
def HodgeTateIsoStatement : Prop := ∀ i, Function.Bijective ((hodgeTateMap P hP r).app i)

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.9" (partial := special) "多項式代数の場合の Hodge–Tate 写像（BS-D68 停止点 3）。一般の R は不要 ／ 11-10 更新（2）"] _root_.SerrePositivity.BhattScholze.Prismatic.hodgeTateMap
attribute [cite BS19 "Thm 4.11" (partial := component) "主張の型（HodgeTateIsoStatement）と結晶基底 (Z_p,(p)) の場合は本体（BS-D68）。一般の有界向き付き基底への帰着（Prop 6.2・Thm 6.3）は drafts ／ 11-10 更新（2）。本体の HodgeTateIsoStatement は Rem 4.19 の鎖複体の模型（reducedModel）のコホモロジーについての主張で、site の RΓ ではない ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.HodgeTateIsoStatement
attribute [cite BS19 "Thm 6.3" (partial := component) "特別な場合：p 完備多項式代数 (A/d)⟨X_1..X_r⟩ だけ（Lemma 4.21 の étale 局所化は不要）。HT 写像と H^* は Čech–Alexander 模型の上（D27）。HT 写像 hodgeTateMap と主張の型 HodgeTateIsoStatement は本体、結晶基底 (ℤ_p,(p)) の場合の同型も本体（hodgeTate_of_deRham_cartier、D68）。一般の向き付き基底の同型 hodgeTate_iso は drafts ／ 11-12 夜更新"] _root_.SerrePositivity.BhattScholze.Prismatic.HodgeTateIsoStatement
attribute [cite BS19 "Thm 6.3" (partial := component) "特別な場合：p 完備多項式代数 (A/d)⟨X_1..X_r⟩ だけ（Lemma 4.21 の étale 局所化は不要）。HT 写像と H^* は Čech–Alexander 模型の上（D27）。HT 写像 hodgeTateMap と主張の型 HodgeTateIsoStatement は本体、結晶基底 (ℤ_p,(p)) の場合の同型も本体（hodgeTate_of_deRham_cartier、D68）。一般の向き付き基底の同型 hodgeTate_iso は drafts ／ 11-12 夜更新"] _root_.SerrePositivity.BhattScholze.Prismatic.hodgeTateMap
