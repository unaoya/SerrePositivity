module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PadicIntMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PadicIntMap

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingInterface
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.CommutativeAlgebra.RootTower.Perfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison

/-!
# 根を添加した perfectoid 基底と完備な底変換

## 概要
ℤ_p に p の両立する p 冪根を添加した環の導来 p 完備化 R₀ は整 perfectoid。
p 完備な環 S の R₀ への完備な底変換と、根を持つ試験環への射を構成する。

## 方針
多項式商を一変数の根の塔の余極限と比較し、完備化と mod p の Frobenius の計算を
既存の塔から移す。整数の完備化は各段を ℤ/pⁿℤ と比較する。

## 規約
完備化は導来完備化の H⁰。付値環の拡大が与えられれば、同じ拡大に沿って射を延長する。

## 使われ方
BS 著者版 Lemma 8.8 の証明で、任意の p 完備環に根添加を施す前の底変換。
-/

@[expose] public noncomputable section

universe u

open _root_.CategoryTheory _root_.MvPolynomial
open scoped _root_.TensorProduct

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.SerrePositivity.Section2 _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (p : ℕ) [Fact p.Prime]

/-- R₀ の完備化前の表示。X₀ = p と X_{n+1}^p = X_n を課す。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootPolynomial := MvPolynomial ℕ (ULift.{u} (PadicInt p))

def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal : Ideal (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootPolynomial.{u} p) :=
  Ideal.span (insert (MvPolynomial.X 0 - (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootPolynomial.{u} p))
    (Set.range (fun n : ℕ => MvPolynomial.X (n + 1) ^ p - MvPolynomial.X n)))

abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootPolynomial.{u} p ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p

/-- 概要：perfectoid 基底 R₀ := ℤ_p[p^{1/p^∞}]^∧（Type u）。
方針：ℤ_p[X_n : n]/(X_0 − p, X_{n+1}^p − X_n) の p 進完備化。perfectoid 性はこの表示の p 完備化について示す。
規約：固定。導来 perfectoid 化の界面の R とは無関係（全 p 完備環を対象とするため）。
使われ方：`baseExtension`。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing : Type u :=
  (completionRing p (CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p)) : Type u)

/-- R₀ の指定した根。X₀ の像は p。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRoot (n : ℕ) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p :=
  (completionUnit p (CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p))).hom
    (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p) (MvPolynomial.X n))

instance : Algebra (PadicInt p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) :=
  ((completionUnit p (CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p))).hom.comp
    ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p)).comp
      ((MvPolynomial.C : ULift.{u} (PadicInt p) →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootPolynomial.{u} p).comp
        ULift.ringEquiv.symm.toRingHom))).toAlgebra

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot (n : ℕ) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p :=
  Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p) (X n)

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot_zero : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot.{u} p 0 = (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p) := by
  apply sub_eq_zero.mp
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot, ← map_natCast (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p)), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot_succ_pow (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot.{u} p (n + 1) ^ p = _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot.{u} p n := by
  apply sub_eq_zero.mp
  simp only [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot, ← map_pow, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self n)))

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot_pow_of_le (m n : ℕ) (hmn : m ≤ n) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot.{u} p n ^ (p ^ (n - m)) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot.{u} p m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [show n + 1 - m = n - m + 1 by omega, pow_succ, pow_mul', _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot_succ_pow, ih]

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift {T : Type u} [CommRing T]
    (f : ULift.{u} (PadicInt p) →+* T) (ρ : ℕ → T)
    (hzero : ρ 0 = (p : T)) (hpow : ∀ n, ρ (n + 1) ^ p = ρ n) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p →+* T := by
  refine Ideal.Quotient.lift (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p) (MvPolynomial.eval₂Hom f ρ) ?_
  suffices _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p ≤ RingHom.ker (MvPolynomial.eval₂Hom f ρ) from this
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal, Ideal.span_le]
  intro x hx
  rcases hx with rfl | ⟨n, rfl⟩
  · simp [hzero, RingHom.mem_ker]
  · simp [hpow, RingHom.mem_ker]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift_root {T : Type u} [CommRing T]
    (f : ULift.{u} (PadicInt p) →+* T) (ρ : ℕ → T) (hzero) (hpow) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p f ρ hzero hpow (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n) = ρ n := by
  simp [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot, Ideal.Quotient.lift_mk]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift_coeff {T : Type u} [CommRing T]
    (f : ULift.{u} (PadicInt p) →+* T) (ρ : ℕ → T) (hzero) (hpow)
    (a : ULift.{u} (PadicInt p)) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p f ρ hzero hpow (Ideal.Quotient.mk _ (C a)) = f a := by
  simp [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift, Ideal.Quotient.lift_mk]

private abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff := ULift.{u} (PadicInt p)
private abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam : Fin 1 → _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p := fun _ => (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff p)
private abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawTower := Tower (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot (n : ℕ) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawTower.{u} p :=
  towerOf (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n (stageX _ _ p n 0)

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot_zero : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot.{u} p 0 = (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawTower.{u} p) := by
  change towerOf (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p 0 (stageX _ _ p 0 0) = _
  have h := mk_X_pow (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p 0 (0 : Fin 1)
  simp only [pow_zero, pow_one] at h
  rw [show stageX (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p 0 0 =
    algebraMap (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff p) _ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p 0) from h]
  rw [show _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p 0 = (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) from rfl, map_natCast, map_natCast]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot_succ_pow (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot.{u} p (n + 1) ^ p = _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot.{u} p n := by
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot
  rw [← map_pow]
  have h := towerOf_towerMap (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n (n + 1)
    (Nat.le_succ n) (stageX (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n 0)
  rw [towerMap_stageX, show n + 1 - n = 1 by omega, pow_one] at h
  exact h

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientToTower : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawTower.{u} p :=
  _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p (algebraMap _ _) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot_zero p)
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot_succ_pow p)

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient (n : ℕ) :
    TowerStage (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p := by
  let C₀ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p
  let Q := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p
  let f : C₀ →+* Q := (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p)).comp MvPolynomial.C
  refine Ideal.Quotient.lift (towerRel C₀ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n)
    (MvPolynomial.eval₂Hom f (fun _ => _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n)) ?_
  suffices towerRel C₀ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n ≤
    RingHom.ker (MvPolynomial.eval₂Hom f (fun (_ : Fin 1) => _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n)) from this
  rw [towerRel, relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change MvPolynomial.eval₂Hom f (fun (_ : Fin 1) => _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n)
    (X i ^ (p ^ n) - C (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p i)) = 0
  have hcoeff : C (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p i) = (p : MvPolynomial (Fin 1) C₀) := map_natCast C p
  rw [hcoeff, map_sub, map_natCast, map_pow, MvPolynomial.eval₂Hom_X', ← _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot_zero p]
  rw [show p ^ n = p ^ (n - 0) by simp, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot_pow_of_le p 0 n (Nat.zero_le n), sub_self]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_root (n : ℕ) (i : Fin 1) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient.{u} p n (stageX _ _ p n i) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n := by
  simp [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient, stageX, Ideal.Quotient.lift_mk]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_coeff (n : ℕ) (a : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p n (algebraMap _ _ a) = Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootIdeal p) (C a) := by
  change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p n (Ideal.Quotient.mk _ (C a)) = _
  simp [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient, Ideal.Quotient.lift_mk]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_compat (m n : ℕ) (hmn : m ≤ n) :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient.{u} p n).comp
      (towerMapRingHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p m n hmn) =
        _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p m := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p n (towerMap _ _ p m n hmn (algebraMap _ _ a)) =
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p m (algebraMap _ _ a)
    rw [AlgHom.commutes, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_coeff, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_coeff]
  · intro i
    change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p n (towerMap _ _ p m n hmn (stageX _ _ p m i)) =
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p m (stageX _ _ p m i)
    rw [towerMap_stageX]
    have hm := (Ideal.Quotient.mk
      (towerRel (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n)).map_pow (X i) (p ^ (n - m))
    change _ = _ at hm
    rw [hm, (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p n).map_pow]
    change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p n (stageX _ _ p n i) ^ (p ^ (n - m)) =
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p m (stageX _ _ p m i)
    rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_root, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_root, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot_pow_of_le p m n hmn]

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawTower.{u} p →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p := by
  let G := fun n => TowerStage (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n
  let f := fun m n (h : m ≤ n) => ⇑(towerMapRingHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p m n h)
  change Ring.DirectLimit G f →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p
  exact Ring.DirectLimit.lift G f (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p)
    (fun m n h x => DFunLike.congr_fun (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_compat p m n h) x)

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient_stage (n : ℕ)
    (x : TowerStage (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p n) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient p (towerOf _ _ p n x) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient p n x := by
  simp only [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient, towerOf, id_eq, Ring.DirectLimit.lift_of]

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientEquivTower : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p ≃+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawTower.{u} p := by
  refine RingEquiv.ofRingHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientToTower p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient p) ?_ ?_
  · apply Ring.DirectLimit.hom_ext
    intro n
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientToTower p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient p
        (towerOf _ _ p n (algebraMap _ _ a))) = towerOf _ _ p n (algebraMap _ _ a)
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient_stage, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_coeff]
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p _ _ _ _ (Ideal.Quotient.mk _ (C a)) = _
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift_coeff]
      exact IsScalarTower.algebraMap_apply (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff p) (TowerStage _ _ p n) _ a
    · intro i
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientToTower p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient p
        (towerOf _ _ p n (stageX _ _ p n i))) = towerOf _ _ p n (stageX _ _ p n i)
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient_stage, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_root]
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p _ _ _ _ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n) = _
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift_root, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot, Subsingleton.elim i 0]
  · apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p _ _ _ _
        (Ideal.Quotient.mk _ (C a))) = _
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift_coeff]
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient p (towerOf _ _ p 0 (algebraMap _ _ a)) = _
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient_stage, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_coeff]
      rfl
    · intro n
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p _ _ _ _ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n)) =
        _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift_root, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerRoot, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerToRootQuotient_stage,
        _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerStageToQuotient_root]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcCompletedTowerPerfectoid :
    _root_.SerrePositivity.IsIntegralPerfectoid (CompletedTower (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p) p := by
  let A := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p
  let e : A ≃+* PadicInt p := ULift.ringEquiv
  let : IsDomain A := e.injective.isDomain e.toRingHom
  let : CharZero A := e.toRingHom.charZero
  let : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  have hmax : Ideal.span {(p : A)} = IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.symm,
      PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  let Q := A ⧸ Ideal.span {(p : A)}
  have hmap : Ideal.span {(p : PadicInt p)} = (Ideal.span {(p : A)}).map e.toRingHom := by
    simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  let q : Q ≃+* ZMod p :=
    (Ideal.quotientEquiv _ _ e hmap).trans
      ((Ideal.quotEquivOfEq PadicInt.maximalIdeal_eq_span_p.symm).trans PadicInt.residueField)
  let : CharP Q p := charP_of_injective_ringHom (f := q.symm.toRingHom) q.symm.injective p
  have hstage : Function.Surjective (stageModPFrobenius A (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p 1) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨algebraMap A _ a, ?_⟩
    rw [stageModPFrobenius_algebraMap, pow_one]
    apply q.injective
    rw [map_pow]
    exact DFunLike.congr_fun (ZMod.frobenius_zmod p) _
  have hp : IsSMulRegular A (p : A) :=
    mul_right_injective₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hdim : ringKrullDim A = 0 + 1 := by
    simpa using IsDiscreteValuationRing.ringKrullDim_eq_one A
  have ht : Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam.{u} p)) = IsLocalRing.maximalIdeal A := by
    rw [show Set.range (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam.{u} p) = {(p : A)} by ext; simp]
    exact hmax
  exact completedTower_isIntegralPerfectoid_of_parameters A p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) hp ht rfl hdim
    (completedTower_modP_pow_surjective_of_stageFrobenius_surjective A (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p hstage)

/-- (R₀) の整 perfectoid 性。一変数の根の塔とその完備化を比較する。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing_isPerfectoid : _root_.SerrePositivity.IsIntegralPerfectoid (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) p := by
  let T := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawTower.{u} p
  let A := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerCoeff.{u} p
  let f : CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p) ≅ CommRingCat.of T :=
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientEquivTower.{u} p).toCommRingCatIso
  let e := (ringCompletionFunctor p).mapIso f
  let := principalCompletionCommRing T (p : T)
  let := principalCompletionAlgebra T (p : T)
  let := flat_tower_over_base A (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTowerParam p) p
  let eA : A ≃+* PadicInt p := ULift.ringEquiv
  let : IsDomain A := eA.injective.isDomain eA.toRingHom
  let : CharZero A := eA.toRingHom.charZero
  have hp : IsSMulRegular A (p : A) :=
    mul_right_injective₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hT := hp.of_flat (S := T)
  rw [map_natCast (algebraMap A T) p] at hT
  let j := principalCompletionAdicAlgEquiv T (p : T) hT
  exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p
    (j.toRingEquiv.symm.trans e.symm.commRingCatIsoToRingEquiv) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcCompletedTowerPerfectoid p)


/-- 試験環の条件。整域である階数 1 の付値環で、p 進完備。 -/
structure _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing (V : Type u) [CommRing V] : Prop where
  isDomain : IsDomain V
  valuationRing : @ValuationRing V _ isDomain
  krullDim_eq_one : ringKrullDim V = 1
  adicComplete : IsAdicComplete (Ideal.span {(p : V)}) V

omit [Fact p.Prime] in
/-- p 進完備な試験付値環は導来 p 完備。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing.isModuleComplete {V : Type u} [CommRing V]
    (hV : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p V) :
    IsModuleComplete V (p : V) (ModuleCat.of V V) := by
  let := hV.adicComplete
  exact isModuleComplete_of_isAdicComplete V (p : V) _

/-- 完備化する直前の S ⊗_{ℤ_p} R₀。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : CommRingCat.{u} := by
  letI := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p S hS).toAlgebra
  exact CommRingCat.of (S ⊗[PadicInt p] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p)

/-- 概要：前段 S₀ := completionRing(S ⊗_{ℤ_p} R₀)（p 完備な R₀ 代数）と単位 S → S₀。
方針：`completionRing`（H⁰(LΛ_p)、既存）と `Algebra.TensorProduct`。
規約：#S₀ ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ（`baseExtension_cardinal_le`）。
使われ方：`exists_perfectoid_arcCover`。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : Type u :=
  (completionRing p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS) : Type u)

/-- R₀ への完備な底変換は導来 p 完備。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension_isModuleComplete (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    IsModuleComplete (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS) (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS)
      (ModuleCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS)) :=
  completionRing_complete p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS)

instance (S : Type u) [CommRing S] (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    Algebra (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS) := by
  letI := (arcPadicIntMap p S hS).toAlgebra
  exact ((completionUnit p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS)).hom.comp
    (Algebra.TensorProduct.includeRight : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p →ₐ[PadicInt p]
      S ⊗[PadicInt p] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p).toRingHom).toAlgebra

def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : S →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS := by
  letI := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p S hS).toAlgebra
  exact (completionUnit p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS)).hom.comp
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[PadicInt p] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p)

theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing_toValuationExtension (W : CommRingCat.{u})
    (hW : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W) (ρ : ℕ → W)
    (hzero : ρ 0 = (p : W)) (hpow : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃ b : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p →+* W, ∀ n, b (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRoot p n) = ρ n := by
  let hWc := hW.isModuleComplete p
  let f := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift p ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p W hWc).comp ULift.ringEquiv.toRingHom)
    ρ hzero hpow
  let f' : CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p) ⟶ W := CommRingCat.ofHom f
  let g := completionLift p f' hWc
  refine ⟨g.hom, fun n => ?_⟩
  have hg := congrArg CommRingCat.Hom.hom (completionLift_comp p f' hWc)
  change ((g.hom).comp (completionUnit p _).hom) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRawRoot p n) = ρ n
  rw [show g.hom.comp (completionUnit p _).hom = f from hg]
  exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotientLift_root p _ ρ hzero hpow n

/-- S → V と R₀ → W から、与えられた拡大 V → W に沿って S₀ → W を構成する。
二つの脚は ℤ_p 上で一致する。テンソルの普遍性と、W の完備性を使う。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_baseExtension_lift_of_map (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (V W : CommRingCat.{u}) (_hV : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p V)
    (hW : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W) (k : S →+* V) (e : V →+* W)
    (_he : e.FaithfullyFlat) (b : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p →+* W) :
    ∃ l : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS →+* W,
      l.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p S hS) = e.comp k ∧
      l.comp (algebraMap (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS)) = b := by
  let hWc := hW.isModuleComplete p
  let : Algebra (PadicInt p) S := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p S hS).toAlgebra
  let : Algebra (PadicInt p) W := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p W hWc).toAlgebra
  let : Algebra S W := (e.comp k).toAlgebra
  have hleft := _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap_unique p W hWc ((e.comp k).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p S hS))
  let : IsScalarTower (PadicInt p) S W := IsScalarTower.of_algebraMap_eq' hleft.symm
  let b' : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p →ₐ[PadicInt p] W :=
    ⟨b, DFunLike.congr_fun (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap_unique p W hWc
      (b.comp (algebraMap (PadicInt p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p))))⟩
  let f := AlgHom.liftEquiv (PadicInt p) S (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) W b'
  let g := completionLift p (S := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS) (CommRingCat.ofHom f.toRingHom) hWc
  have hg : g.hom.comp (completionUnit p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS)).hom = f.toRingHom :=
    congrArg CommRingCat.Hom.hom (completionLift_comp p (CommRingCat.ofHom f.toRingHom) hWc)
  refine ⟨g.hom, ?_, ?_⟩
  · change g.hom.comp ((completionUnit p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS)).hom.comp
      Algebra.TensorProduct.includeLeftRingHom) = e.comp k
    rw [← RingHom.comp_assoc, hg]
    exact RingHom.ext f.commutes
  · change g.hom.comp ((completionUnit p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS)).hom.comp
      (Algebra.TensorProduct.includeRight : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p →ₐ[PadicInt p]
        S ⊗[PadicInt p] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p).toRingHom) = b
    rw [← RingHom.comp_assoc, hg]
    exact RingHom.ext (fun a => DFunLike.congr_fun
      ((AlgHom.liftEquiv (PadicInt p) S (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) W).left_inv b') a)

end SerrePositivity.BhattScholze.Perfectoidization.Derived
