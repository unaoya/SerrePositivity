module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Andre.Transfinite.Limit
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Etale.Weakly

/-!
# 整閉包とその完備化への付値環の延長

## 概要
BS 著者版 Theorem 10.9・10.11 の証明で使う Corollary 8.12 の環論的入力を与える。

## 方針
被約化の主局所化内で整閉包を取る。付値環への射を被約化経由で整閉包へ延ばし、
完備化の普遍性でさらに延ばす。

## 規約
局所化の比較には被約化からの射を用いる。完備化は導来完備化の H⁰ で取る。

## 使われ方
Lemma 10.12 の層ごとに整閉包の完備化を比較する。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open PerfectoidizationInterface SerrePositivity.DerivedCompletion
open SerrePositivity.BhattScholze.Andre.Transfinite

variable (p : ℕ) (R : Type u) [CommRing R]

private theorem image_ne_zero_of_not_span_le_ker {A W : Type u} [CommRing A] [CommRing W]
    (k : A →+* W) (g : A) (h : ¬ Ideal.span {g} ≤ RingHom.ker k) : k g ≠ 0 := by
  intro hg
  apply h
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hg))

/-- Corollary 8.12 の付値環への一意延長条件を、整性と主局所化の同型から得る。 -/
theorem arcOutside_of_integral_of_localization_iso {U V : A_R R} (f : U ⟶ V) (g : U.right)
    (hint : f.right.hom.IsIntegral)
    (hloc : Function.Bijective (Localization.awayMap f.right.hom g)) :
    ArcOutside R p f (Ideal.span {g}) := by
  intro W _ _ _ _ _ k hk
  let := f.right.hom.toAlgebra
  let := k.toAlgebra
  let : Algebra.IsIntegral U.right V.right := ⟨hint⟩
  exact existsUnique_valuation_extension_of_integral_away_bijective U.right V.right W g
    (image_ne_zero_of_not_span_le_ker k g hk) hloc

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Lemma 10.12 の層で用いる被約化の主局所化。 -/
abbrev reducedAway (g : R) := Localization.Away (algebraMap R (S ⧸ nilradical S) g)

/-- 被約化を経由する、主局所化上の元の基底環の作用。 -/
@[instance_reducible]
def reducedAwayBase (g : R) : Algebra R (reducedAway R S g) :=
  ((algebraMap (S ⧸ nilradical S) (reducedAway R S g)).comp
    (algebraMap R (S ⧸ nilradical S))).toAlgebra

attribute [local instance] reducedAwayBase

/-- Theorem 10.11 の証明に現れる、被約化の主局所化内の整閉包。 -/
def integralClosureInLocalization (g : R) : Subalgebra R (reducedAway R S g) :=
  integralClosure R (reducedAway R S g)

/-- 被約化から Theorem 10.11 の整閉包への標準写像。 -/
def reductionToIntegralClosure (g : R) (h : Algebra.IsIntegral R S) :
    (S ⧸ nilradical S) →ₐ[R] integralClosureInLocalization R S g := by
  let f : (S ⧸ nilradical S) →ₐ[R] reducedAway R S g :=
    { __ := algebraMap (S ⧸ nilradical S) _
      commutes' := fun _ => rfl }
  refine f.codRestrict _ ?_
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  let q := f.comp (Ideal.Quotient.mkₐ R (nilradical S))
  change (algebraMap R (reducedAway R S g)).IsIntegralElem (q s)
  rw [← q.comp_algebraMap]
  exact RingHom.IsIntegralElem.map (h.isIntegral s) q.toRingHom

/-- Theorem 10.11 の比較写像。被約化を経由して整閉包に入る。 -/
def toIntegralClosure (g : R) (h : Algebra.IsIntegral R S) :
    S →ₐ[R] integralClosureInLocalization R S g :=
  (reductionToIntegralClosure R S g h).comp (Ideal.Quotient.mkₐ R (nilradical S))

/-- Theorem 10.11 の比較写像を離散 R 代数の圏で表す。 -/
def closureArrow (g : R) (h : Algebra.IsIntegral R S) :
    ofAlgebra R S ⟶ ofAlgebra R (integralClosureInLocalization R S g) :=
  Under.homMk (CommRingCat.ofHom (toIntegralClosure R S g h).toRingHom) <|
    CommRingCat.hom_ext (toIntegralClosure R S g h).comp_algebraMap

/-- Theorem 10.11 の比較写像の整性。 -/
theorem integralClosureInLocalization_integral (g : R) (h : Algebra.IsIntegral R S) :
    (toIntegralClosure R S g h).toRingHom.IsIntegral := by
  let f := toIntegralClosure R S g h
  apply RingHom.IsIntegral.tower_top (algebraMap R S) f.toRingHom
  exact f.comp_algebraMap.symm ▸
    (show (algebraMap R (integralClosureInLocalization R S g)).IsIntegral from fun x =>
      (isIntegral_algHom_iff (integralClosureInLocalization R S g).val
        Subtype.val_injective).mp x.property)

private theorem reductionToIntegralClosure_integral (g : R) (h : Algebra.IsIntegral R S) :
    (reductionToIntegralClosure R S g h).toRingHom.IsIntegral := by
  apply RingHom.IsIntegral.tower_top (Ideal.Quotient.mk (nilradical S))
  change (toIntegralClosure R S g h).toRingHom.IsIntegral
  exact integralClosureInLocalization_integral R S g h

private theorem reductionToIntegralClosure_away_bijective (g : R) (h : Algebra.IsIntegral R S) :
    Function.Bijective (Localization.awayMap (reductionToIntegralClosure R S g h).toRingHom
      (algebraMap R (S ⧸ nilradical S) g)) := by
  let a := algebraMap R (S ⧸ nilradical S) g
  let B := reducedAway R S g
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro x hx
    have hzero : algebraMap (S ⧸ nilradical S) B x = 0 :=
      congrArg Subtype.val hx
    obtain ⟨⟨y, n, rfl⟩, hy⟩ := (IsLocalization.map_eq_zero_iff (.powers a) B x).mp hzero
    exact ⟨n, hy⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro x
    refine ⟨(IsLocalization.Away.sec a (x : B)).1, (IsLocalization.Away.sec a (x : B)).2, ?_⟩
    apply Subtype.ext
    change algebraMap (S ⧸ nilradical S) B (IsLocalization.Away.sec a (x : B)).1 =
      (algebraMap (S ⧸ nilradical S) B a) ^ (IsLocalization.Away.sec a (x : B)).2 * (x : B)
    rw [← map_pow, mul_comm]
    exact (IsLocalization.Away.sec_spec a (x : B)).symm

/-- Theorem 10.11 の比較写像は Corollary 8.12 の付値環条件を満たす。 -/
theorem integralClosureInLocalization_arcOutside (g : R) (h : Algebra.IsIntegral R S) :
    ArcOutside R p (closureArrow R S g h) (Ideal.span {algebraMap R S g}) := by
  intro W _ _ _ _ _ k hk
  let q := Ideal.Quotient.mk (nilradical S)
  let k₀ := Ideal.Quotient.lift (nilradical S) k fun x hx =>
    (IsNilpotent.map (show IsNilpotent x from hx) k).eq_zero
  let f := (reductionToIntegralClosure R S g h).toRingHom
  let := f.toAlgebra
  let := k₀.toAlgebra
  let : Algebra.IsIntegral (S ⧸ nilradical S) (integralClosureInLocalization R S g) :=
    ⟨reductionToIntegralClosure_integral R S g h⟩
  obtain ⟨l, hl, hu⟩ := existsUnique_valuation_extension_of_integral_away_bijective
    (S ⧸ nilradical S) (integralClosureInLocalization R S g) W
    (algebraMap R (S ⧸ nilradical S) g)
    (image_ne_zero_of_not_span_le_ker k (algebraMap R S g) hk)
    (reductionToIntegralClosure_away_bijective R S g h)
  refine ⟨l, ?_, ?_⟩
  · change (l.comp f).comp q = k
    change l.comp f = k₀ at hl
    rw [hl]
    exact Ideal.Quotient.lift_comp_mk _ _ _
  · intro m hm
    apply hu m
    change m.comp f = k₀
    apply RingHom.ext
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact RingHom.congr_fun hm s

/-- Theorem 10.11 の整閉包の導来 p 完備化の H⁰。 -/
def integralClosureCompletion (g : R) : A_R R :=
  (completionFunctor p R).obj (ofAlgebra R (integralClosureInLocalization R S g))

/-- Theorem 10.11 で Corollary 8.12 を適用する比較写像。 -/
def completedClosureArrow (g : R) (h : Algebra.IsIntegral R S) :
    ofAlgebra R S ⟶ integralClosureCompletion p R S g :=
  closureArrow R S g h ≫ (completionAlgebraUnit p R).app _

set_option backward.isDefEq.respectTransparency false in
/-- 整閉包の完備化への比較も Corollary 8.12 の付値環条件を満たす。 -/
theorem arcOutside_completionRing (g : R) (h : Algebra.IsIntegral R S) :
    ArcOutside R p (completedClosureArrow p R S g h) (Ideal.span {algebraMap R S g}) := by
  intro W _ _ _ hw hcomplete k hk
  let := hcomplete
  have hW := isModuleComplete_of_isAdicComplete W (p : W) (ModuleCat.of W W)
  obtain ⟨l, hl, hu⟩ := integralClosureInLocalization_arcOutside p R S g h W hw hcomplete k hk
  let T := (ofAlgebra R (integralClosureInLocalization R S g)).right
  let f : T ⟶ CommRingCat.of W := CommRingCat.ofHom l
  obtain ⟨m, hm, _⟩ := completion_existsUnique p f hW
  have hrestrict : m.hom.comp (completionUnit p T).hom = l :=
    congrArg (fun q : T ⟶ CommRingCat.of W => q.hom) hm
  refine ⟨m.hom, ?_, ?_⟩
  · change (m.hom.comp (completionUnit p T).hom).comp (closureArrow R S g h).right.hom = k
    rw [hrestrict, hl]
  · intro n hn
    change (n.comp (completionUnit p T).hom).comp (closureArrow R S g h).right.hom = k at hn
    let m₀ : T →+* W := n.comp (completionUnit p T).hom
    have he : m₀ = l := hu m₀ hn
    let := principalCompletionCommRing T (p : T)
    let n' : completionRing p T ⟶ CommRingCat.of W := CommRingCat.ofHom n
    have hncomp : completionUnit p T ≫ n' = f := CommRingCat.hom_ext he
    have hn' := @completion_hom_ext p T (CommRingCat.of W) hW n' m (hncomp.trans hm.symm)
    exact congrArg (fun q : completionRing p T ⟶ CommRingCat.of W => q.hom) hn'

/-- Theorem 10.9 の証明で用いる、主局所化の有限エタール性。 -/
def FiniteEtaleAway (g : R) : Prop :=
  let := GenericEtale.awayAlgebra R S g
  Module.Finite (Localization.Away g) (Localization.Away (algebraMap R S g)) ∧
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))

private theorem integralClosure_p_power_torsion [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (g : R) (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    let T := integralClosureInLocalization R S g
    ∀ n : ℕ, ∀ x : T, (p : T) ^ n * x = 0 → (p : T) ^ 1 * x = 0 := by
  let A := Localization.Away g
  let B := reducedAway R S g
  let := GenericEtale.awayAlgebra R (S ⧸ nilradical S) g
  let : Algebra.Etale (Localization.Away g) (reducedAway R S g) := het.2
  let : IsReduced R := hR.isReduced
  let : IsReduced (Localization.Away g) := inferInstance
  intro T n x hx
  apply Subtype.ext
  have hxB : (p : B) ^ n * (x : B) = 0 := congrArg Subtype.val hx
  have hflat := flat_power_torsion_bound (R := A) (M := B) (p : A) 1
    (fun m y hy => by
      simpa only [pow_one] using mul_eq_zero_of_pow_mul_eq_zero_of_reduced (p : A) y m hy)
    n (x : B)
  have he (m : ℕ) : (p : A) ^ m • (x : B) = (p : B) ^ m * (x : B) := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  exact (he 1).symm.trans (hflat ((he n).trans hxB))

attribute [local instance] HasDerivedCategory.standard

/-- Theorem 10.11 の整閉包の導来完備化は離散で、通常の p 進完備化に一致する。 -/
theorem integralClosureCompletion_isModuleComplete [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (g : R) (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    let T := integralClosureInLocalization R S g
    let C := (integralClosureCompletion p R S g).right
    let I := Ideal.span {(p : T)}
    IsModuleComplete C (p : C) (ModuleCat.of C C) ∧
      (∃ e : C ≃+* AdicCompletion I T,
        e.toRingHom.comp (completionUnit p (CommRingCat.of T)).hom =
          algebraMap T (AdicCompletion I T)) ∧
      ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj
        ((derivedComplexCompletionFunctor T (p : T)).obj
          ((moduleObjectFunctor T).obj (ModuleCat.of T T)))) := by
  dsimp only
  let T := integralClosureInLocalization R S g
  have hbound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T, (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0 :=
    ⟨1, integralClosure_p_power_torsion p R S hR g het⟩
  refine ⟨completionRing_complete p (CommRingCat.of T), ?_, ?_⟩
  · let := principalCompletionCommRing T (p : T)
    let := principalCompletionAlgebra T (p : T)
    let e := boundedPrincipalCompletionAdicAlgEquiv T (p : T) hbound
    refine ⟨e.toRingEquiv, RingHom.ext (fun x => e.commutes x)⟩
  · obtain ⟨hge, hle, _⟩ := completedUnit_pure_bounded_torsion T (p : T) hbound
    intro i hi
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ _).mp hge i hi
    · exact (DerivedCategory.isLE_iff _ _).mp hle i hi

end SerrePositivity.BhattScholze.Perfectoidization.Derived
