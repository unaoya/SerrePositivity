module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCompletion
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Defs

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import SerrePositivity.CommutativeAlgebra.RootTower.Perfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison

/-!
# 導来 p 完備環への標準の p 進整数作用

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MvPolynomial
open scoped TensorProduct

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.Section2 SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (p : ℕ) [Fact p.Prime]

private abbrev intPadicIdeal : Ideal (ULift.{u} ℤ) := Ideal.span {(p : ULift.{u} ℤ)}

private def intPadicLevel (n : ℕ) :
    (ULift.{u} ℤ ⧸ intPadicIdeal.{u} p ^ n) ≃+* ZMod (p ^ n) :=
  (Ideal.quotientEquiv _ (Ideal.span {((p ^ n : ℕ) : ℤ)})
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    (by rw [intPadicIdeal, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
        map_pow, map_natCast, Nat.cast_pow])).trans
    (Int.quotientSpanNatEquivZMod _)

omit [Fact p.Prime] in
private theorem intPadicLevel_factor {m n : ℕ} (hmn : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))).comp (intPadicLevel.{u} p n).toRingHom =
      (intPadicLevel.{u} p m).toRingHom.comp (Ideal.Quotient.factorPow (intPadicIdeal p) hmn) := by
  apply Ideal.Quotient.ringHom_ext
  exact RingHom.ext fun x => by
    have hx : x = (x.down : ℤ) := by cases x; rfl
    rw [hx, map_intCast, map_intCast]

private def padicIntLevelHom (n : ℕ) :
    AdicCompletion (intPadicIdeal.{u} p) (ULift.{u} ℤ) →+* ZMod (p ^ n) :=
  (intPadicLevel.{u} p n).toRingHom.comp (AdicCompletion.evalₐ (intPadicIdeal.{u} p) n).toRingHom

omit [Fact p.Prime] in
private theorem padicIntLevelHom_compat (m n : ℕ) (hmn : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))).comp (padicIntLevelHom.{u} p n) =
      padicIntLevelHom.{u} p m := by
  unfold padicIntLevelHom
  rw [← RingHom.comp_assoc, intPadicLevel_factor.{u} p hmn, RingHom.comp_assoc]
  congr 1
  ext x : 1
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (intPadicIdeal.{u} p) (ULift.{u} ℤ) x
  change Ideal.Quotient.factorPow (intPadicIdeal p) hmn
    (AdicCompletion.evalₐ (intPadicIdeal.{u} p) n (AdicCompletion.mk _ _ s)) =
      AdicCompletion.evalₐ (intPadicIdeal.{u} p) m (AdicCompletion.mk _ _ s)
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (intPadicIdeal p ^ m) (s n) =
    Ideal.Quotient.mk (intPadicIdeal p ^ m) (s m)
  apply Ideal.Quotient.eq.mpr
  simpa [SModEq.sub_mem, Ideal.mul_top] using (s.property hmn).symm

private def padicIntFromCompletion :
    AdicCompletion (intPadicIdeal.{u} p) (ULift.{u} ℤ) →+* PadicInt p :=
  PadicInt.lift (padicIntLevelHom_compat.{u} p)

private theorem padicIntFromCompletion_spec (n : ℕ)
    (x : AdicCompletion (intPadicIdeal.{u} p) (ULift.{u} ℤ)) :
    PadicInt.toZModPow n (padicIntFromCompletion.{u} p x) =
      intPadicLevel.{u} p n (AdicCompletion.evalₐ (intPadicIdeal.{u} p) n x) :=
  DFunLike.congr_fun (PadicInt.lift_spec (padicIntLevelHom_compat.{u} p) n) x

private def padicIntCompletionEquiv :
    AdicCompletion (intPadicIdeal.{u} p) (ULift.{u} ℤ) ≃+* PadicInt p := by
  refine RingEquiv.ofBijective (padicIntFromCompletion.{u} p) ⟨?_, ?_⟩
  · intro x y h
    apply AdicCompletion.ext_evalₐ
    intro n
    apply (intPadicLevel.{u} p n).injective
    rw [← padicIntFromCompletion_spec, ← padicIntFromCompletion_spec, h]
  · intro y
    let f (n : ℕ) :=
      (intPadicLevel.{u} p n).symm.toRingHom.comp (PadicInt.toZModPow (p := p) n)
    have hf {m n : ℕ} (hmn : m ≤ n) :
        (Ideal.Quotient.factorPow (intPadicIdeal p) hmn).comp (f n) = f m := by
      ext x : 1
      apply (intPadicLevel.{u} p m).injective
      have hfactor := DFunLike.congr_fun (intPadicLevel_factor.{u} p hmn) (f n x)
      change (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)))
        (intPadicLevel.{u} p n (f n x)) =
          intPadicLevel.{u} p m (Ideal.Quotient.factorPow (intPadicIdeal p) hmn (f n x)) at hfactor
      change intPadicLevel.{u} p m (Ideal.Quotient.factorPow (intPadicIdeal p) hmn (f n x)) =
        intPadicLevel.{u} p m (f m x)
      rw [← hfactor]
      change (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)))
        (intPadicLevel.{u} p n ((intPadicLevel.{u} p n).symm (PadicInt.toZModPow n x))) =
          intPadicLevel.{u} p m ((intPadicLevel.{u} p m).symm (PadicInt.toZModPow m x))
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact PadicInt.cast_toZModPow m n hmn x
    refine ⟨AdicCompletion.liftRingHom (intPadicIdeal p) f hf y, ?_⟩
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [padicIntFromCompletion_spec, AdicCompletion.evalₐ_liftRingHom]
    exact (intPadicLevel.{u} p n).apply_symm_apply _

private abbrev liftedIntegers : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)

private def intCompletionEquivPadic :
    letI := principalCompletionCommRing (ULift.{u} ℤ) (p : ULift.{u} ℤ)
    PrincipalCompletionH0 (ULift.{u} ℤ) (p : ULift.{u} ℤ) ≃+* PadicInt p := by
  letI := principalCompletionCommRing (ULift.{u} ℤ) (p : ULift.{u} ℤ)
  letI := principalCompletionAlgebra (ULift.{u} ℤ) (p : ULift.{u} ℤ)
  let e : ULift.{u} ℤ ≃+* ℤ := ULift.ringEquiv
  let : IsDomain (ULift.{u} ℤ) := e.injective.isDomain e.toRingHom
  let : CharZero (ULift.{u} ℤ) := e.toRingHom.charZero
  have hp : IsSMulRegular (ULift.{u} ℤ) (p : ULift.{u} ℤ) :=
    mul_right_injective₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  exact (principalCompletionAdicAlgEquiv (ULift.{u} ℤ) (p : ULift.{u} ℤ) hp).toRingEquiv.trans
    (padicIntCompletionEquiv.{u} p)

private def liftedIntMap (S : Type u) [CommRing S] : ULift.{u} ℤ →+* S :=
  (Int.castRingHom S).comp ULift.ringEquiv.toRingHom

/-- 導来 p 完備な離散環への標準 ℤ_p 作用。 -/
@[no_expose] def arcPadicIntMap (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : PadicInt p →+* S := by
  let l := completionLift p (S := liftedIntegers.{u}) (T := CommRingCat.of S)
    (CommRingCat.ofHom (liftedIntMap S)) hS
  let e : (completionRing p liftedIntegers.{u} : Type u) ≃+* PadicInt p :=
    intCompletionEquivPadic p
  exact l.hom.comp e.symm.toRingHom

/-- 導来 p 完備な離散環への ℤ_p からの環射は標準の射に一致する。 -/
theorem arcPadicIntMap_unique (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) (g : PadicInt p →+* S) :
    g = arcPadicIntMap p S hS := by
  let e : (completionRing p liftedIntegers.{u} : Type u) ≃+* PadicInt p :=
    intCompletionEquivPadic p
  let l := completionLift p (S := liftedIntegers.{u}) (T := CommRingCat.of S)
    (CommRingCat.ofHom (liftedIntMap S)) hS
  have h : CommRingCat.ofHom (g.comp e.toRingHom) = l := by
    apply completion_hom_ext p (S := liftedIntegers.{u}) (T := CommRingCat.of S) hS
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => by
      have hx : x = (x.down : ℤ) := by cases x; rfl
      rw [hx, map_intCast, map_intCast]
  have hg : g.comp e.toRingHom = l.hom := congrArg CommRingCat.Hom.hom h
  change g = l.hom.comp e.symm.toRingHom
  rw [← hg]
  ext x
  exact congrArg g (e.apply_symm_apply x).symm



end SerrePositivity.BhattScholze.Perfectoidization.Derived
