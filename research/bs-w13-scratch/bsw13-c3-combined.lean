module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Andre.Transfinite.Limit
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Integral


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



/-!
# 整代数の有限表示有限近似

## 概要
BS 著者版 Theorem 10.11 の証明で用いる整代数の filtered 余極限表示を構成する。

## 方針
有限個の変数と有限個の関係を選び、各変数について整性を表すモニック関係を加える。

## 規約
近似から元の代数への射は一般の代数準同型とする。

## 使われ方
有限表示有限の場合の結論を任意の整代数に移す。
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open PerfectoidizationInterface

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Theorem 10.11 の有限表示有限 R 代数の条件。 -/
def FinitePresentedFinite (U : A_R R) : Prop :=
  letI := U.hom.hom.toAlgebra
  Module.Finite R U.right ∧ Algebra.FinitePresentation R U.right

private def ApproximationIndex :=
  { i : Finset S × Finset (MvPolynomial S R) //
    ∀ q ∈ i.2, q.vars ⊆ i.1 ∧ MvPolynomial.aeval (R := R) (id : S → S) q = 0 }

private instance : Preorder (ApproximationIndex R S) := inferInstanceAs
  (Preorder { _i : Finset S × Finset (MvPolynomial S R) // _ })

private instance : Nonempty (ApproximationIndex R S) :=
  ⟨⟨(∅, ∅), by intro q hq; exact (Finset.notMem_empty q hq).elim⟩⟩

private instance : IsDirectedOrder (ApproximationIndex R S) where
  directed i j := by
    classical
    refine ⟨⟨(i.1.1 ∪ j.1.1, i.1.2 ∪ j.1.2), ?_⟩, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hi | hj
      · exact ⟨(i.2 q hi).1.trans Finset.subset_union_left, (i.2 q hi).2⟩
      · exact ⟨(j.2 q hj).1.trans Finset.subset_union_right, (j.2 q hj).2⟩
    · exact ⟨Finset.subset_union_left, Finset.subset_union_left⟩
    · exact ⟨Finset.subset_union_right, Finset.subset_union_right⟩

variable {R S}

private abbrev Var (i : ApproximationIndex R S) := {x // x ∈ i.1.1}
private abbrev StagePolynomial (i : ApproximationIndex R S) := MvPolynomial (Var i) R

private def restrictRelation (i : ApproximationIndex R S) (q : {q // q ∈ i.1.2}) :
    StagePolynomial i :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range q.1 (Subtype.val : Var i → S)
    Subtype.val_injective (by simpa using (i.2 q.1 q.2).1)).choose

private theorem rename_restrictRelation (i : ApproximationIndex R S) (q : {q // q ∈ i.1.2}) :
    MvPolynomial.rename (Subtype.val : Var i → S) (restrictRelation i q) = q :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range q.1 (Subtype.val : Var i → S)
    Subtype.val_injective (by simpa using (i.2 q.1 q.2).1)).choose_spec

private def relations (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S) :
    Set (StagePolynomial i) :=
  Set.range (restrictRelation i) ∪
    Set.range (fun x : Var i => ((h.isIntegral x.1).choose).toMvPolynomial x)

private def stage (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S) :=
  StagePolynomial i ⧸ Ideal.span (relations h i)

private instance (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S) :
    CommRing (stage h i) := inferInstanceAs (CommRing (_ ⧸ _))

private instance (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S) :
    Algebra R (stage h i) := inferInstanceAs (Algebra R (_ ⧸ _))

private def stageQuotient (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S) :
    StagePolynomial i →ₐ[R] stage h i := Ideal.Quotient.mkₐ R _

private def stageToAlgebra (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S) :
    stage h i →ₐ[R] S := by
  apply Ideal.Quotient.liftₐ _ (MvPolynomial.aeval Subtype.val)
  apply (Ideal.span_le.mpr ?_ : Ideal.span (relations h i) ≤ RingHom.ker _)
  rintro _ (⟨q, rfl⟩ | ⟨x, rfl⟩)
  · change MvPolynomial.aeval Subtype.val (restrictRelation i q) = 0
    rw [← show MvPolynomial.aeval (R := R) (id : S → S)
      (MvPolynomial.rename (Subtype.val : Var i → S) (restrictRelation i q)) =
        MvPolynomial.aeval Subtype.val (restrictRelation i q) from MvPolynomial.aeval_rename _ _ _]
    rw [rename_restrictRelation]
    exact (i.2 q.1 q.2).2
  · change MvPolynomial.aeval Subtype.val (((h.isIntegral x.1).choose).toMvPolynomial x) = 0
    rw [MvPolynomial.aeval_toMvPolynomial]
    exact (h.isIntegral x.1).choose_spec.2

private def varInclusion {i j : ApproximationIndex R S} (hij : i ≤ j) : Var i → Var j :=
  fun x => ⟨x.1, hij.1 x.2⟩

private def stageMap (h : Algebra.IsIntegral R S) {i j : ApproximationIndex R S} (hij : i ≤ j) :
    stage h i →ₐ[R] stage h j := by
  let f := (stageQuotient h j).comp (MvPolynomial.rename (varInclusion hij))
  apply Ideal.Quotient.liftₐ _ f
  apply (Ideal.span_le.mpr ?_ : Ideal.span (relations h i) ≤ RingHom.ker f.toRingHom)
  rintro _ (⟨q, rfl⟩ | ⟨x, rfl⟩)
  · have he : MvPolynomial.rename (varInclusion hij) (restrictRelation i q) =
        restrictRelation j ⟨q.1, hij.2 q.2⟩ := by
      apply MvPolynomial.rename_injective (Subtype.val : Var j → S) Subtype.val_injective
      rw [MvPolynomial.rename_rename, rename_restrictRelation j]
      exact rename_restrictRelation i q
    change stageQuotient h j (MvPolynomial.rename (varInclusion hij) (restrictRelation i q)) = 0
    rw [he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨_, rfl⟩))
  · change stageQuotient h j
      (MvPolynomial.rename (varInclusion hij) (((h.isIntegral x.1).choose).toMvPolynomial x)) = 0
    rw [MvPolynomial.rename_toMvPolynomial]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inr ⟨varInclusion hij x, rfl⟩))

private theorem stageMap_quotient (h : Algebra.IsIntegral R S) {i j : ApproximationIndex R S}
    (hij : i ≤ j) (q : StagePolynomial i) :
    stageMap h hij (stageQuotient h i q) =
      stageQuotient h j (MvPolynomial.rename (varInclusion hij) q) :=
  rfl

private theorem stage_finite (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S) :
    Module.Finite R (stage h i) ∧ Algebra.FinitePresentation R (stage h i) := by
  have hp : Algebra.FinitePresentation R (stage h i) :=
    Algebra.FinitePresentation.quotient
      (Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _)))
  let := hp
  suffices hi : Algebra.IsIntegral R (stage h i) from ⟨hi.finite, hp⟩
  have hi (x : Var i) : IsIntegral R (stageQuotient h i (MvPolynomial.X x)) := by
    refine ⟨(h.isIntegral x.1).choose, (h.isIntegral x.1).choose_spec.1, ?_⟩
    change Polynomial.aeval (stageQuotient h i (MvPolynomial.X x)) (h.isIntegral x.1).choose = 0
    rw [Polynomial.aeval_algHom_apply]
    have hz : stageQuotient h i (((h.isIntegral x.1).choose).toMvPolynomial x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨x, rfl⟩))
    rwa [Polynomial.toMvPolynomial] at hz
  apply integralClosure_eq_top_iff.mp
  apply top_unique
  have he : Algebra.adjoin R
      (Set.range (fun x : Var i => stageQuotient h i (MvPolynomial.X x))) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    have hmap : MvPolynomial.aeval (fun x : Var i => stageQuotient h i (MvPolynomial.X x)) =
        stageQuotient h i := (MvPolynomial.aeval_unique _).symm
    rw [hmap]
    exact (AlgHom.range_eq_top _).mpr Ideal.Quotient.mk_surjective
  rw [← he]
  exact Algebra.adjoin_le fun _ ⟨x, hx⟩ => hx ▸ hi x

private def stageArrow {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : ofAlgebra R A ⟶ ofAlgebra R B :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (CommRingCat.hom_ext f.comp_algebraMap)

private def approximationDiagram (h : Algebra.IsIntegral R S) : ApproximationIndex R S ⥤ A_R R where
  obj i := ofAlgebra R (stage h i)
  map k := stageArrow (stageMap h (leOfHom k))
  map_id i := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    change stageMap h _ (stageQuotient h i q) = stageQuotient h i q
    rw [stageMap_quotient]
    exact congrArg (stageQuotient h i) (MvPolynomial.rename_id_apply q)
  map_comp {i j k} f g := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    change stageMap h _ (stageQuotient h i q) = stageMap h _ (stageMap h _ (stageQuotient h i q))
    simp only [stageMap_quotient, MvPolynomial.rename_rename]
    rfl

private def approximationCocone (h : Algebra.IsIntegral R S) : Cocone (approximationDiagram h) where
  pt := ofAlgebra R S
  ι :=
    { app := fun i => stageArrow (stageToAlgebra h i)
      naturality := by
        intro i j k
        apply Under.UnderMorphism.ext
        apply CommRingCat.hom_ext
        ext x
        obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
        change stageToAlgebra h j (stageMap h _ (stageQuotient h i q)) =
          stageToAlgebra h i (stageQuotient h i q)
        rw [stageMap_quotient]
        exact MvPolynomial.aeval_rename _ _ _ }

private theorem stageCanKill (h : Algebra.IsIntegral R S) (i : ApproximationIndex R S)
    (rels : Finset (StagePolynomial i))
    (hrel : ∀ q ∈ rels, MvPolynomial.aeval (R := R) (Subtype.val : Var i → S) q = 0) :
    ∃ (j : ApproximationIndex R S) (hij : i ≤ j),
      Function.Surjective (stageMap h hij) ∧
      ∀ q ∈ rels, stageMap h hij (stageQuotient h i q) = 0 := by
  classical
  let rename := MvPolynomial.rename (R := R) (Subtype.val : Var i → S)
  let j : ApproximationIndex R S := ⟨(i.1.1, i.1.2 ∪ rels.image rename), by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact i.2 s hs
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hs
      constructor
      · intro v hv
        obtain ⟨w, hw⟩ := MvPolynomial.mem_vars_rename _ _ hv
        exact hw.2 ▸ w.property
      · rw [MvPolynomial.aeval_rename]
        exact hrel q hq⟩
  let hij : i ≤ j := ⟨le_rfl, Finset.subset_union_left⟩
  refine ⟨j, hij, ?_, ?_⟩
  · intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨stageQuotient h i q, ?_⟩
    rw [stageMap_quotient]
    exact congrArg (stageQuotient h j) (MvPolynomial.rename_id_apply q)
  · intro q hq
    let sj : {t // t ∈ j.1.2} := ⟨rename q,
      Finset.mem_union_right _ (Finset.mem_image_of_mem rename hq)⟩
    have heq : MvPolynomial.rename (varInclusion hij) q = restrictRelation j sj := by
      apply MvPolynomial.rename_injective (Subtype.val : Var j → S) Subtype.val_injective
      rw [MvPolynomial.rename_rename, rename_restrictRelation j]
      rfl
    rw [stageMap_quotient, heq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨sj, rfl⟩))

private def approximationCoconeIsColimit (h : Algebra.IsIntegral R S) :
    IsColimit (approximationCocone h) := by
  classical
  let : IsConnected (ApproximationIndex R S) := IsFiltered.isConnected _
  apply isColimitOfReflects (Under.forget (CommRingCat.of R))
  let : ReflectsColimit (approximationDiagram h ⋙ Under.forget (CommRingCat.of R))
      (forget CommRingCat) := reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    let i : ApproximationIndex R S := ⟨({x}, ∅), by simp⟩
    refine ⟨i, stageQuotient h i (MvPolynomial.X ⟨x, Finset.mem_singleton_self _⟩), ?_⟩
    change x = MvPolynomial.aeval (R := R) (Subtype.val : Var i → S)
      (MvPolynomial.X ⟨x, _⟩)
    simp
  · intro i x y he
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    change MvPolynomial.aeval (R := R) (Subtype.val : Var i → S) q =
      MvPolynomial.aeval (R := R) (Subtype.val : Var i → S) r at he
    obtain ⟨j, hij, _, hz⟩ := stageCanKill h i {q - r} (by
      intro t ht
      obtain rfl := Finset.mem_singleton.mp ht
      simpa only [map_sub, sub_eq_zero] using he)
    refine ⟨j, homOfLE hij, ?_⟩
    change stageMap h hij (stageQuotient h i q) = stageMap h hij (stageQuotient h i r)
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact hz _ (Finset.mem_singleton_self _)

/-- Theorem 10.11 の有限表示有限への帰着。整代数は有限表示有限代数の filtered 余極限である。 -/
theorem integral_isFilteredColimit_finitePresentation (h : Algebra.IsIntegral R S) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R S)),
      (∀ i, FinitePresentedFinite R (F.obj i)) ∧ Nonempty (IsColimit (Cocone.mk _ η)) := by
  refine ⟨ApproximationIndex R S, inferInstance, inferInstance, approximationDiagram h,
    (approximationCocone h).ι, ?_, ⟨approximationCoconeIsColimit h⟩⟩
  intro i
  change letI := (algebraMap R (stage h i)).toAlgebra
    Module.Finite R (stage h i) ∧ Algebra.FinitePresentation R (stage h i)
  rw [toAlgebra_algebraMap]
  exact stage_finite h i

section FixedLocalization

variable {B : Type u} [CommRing B] [Algebra R B]
  (h : Algebra.IsIntegral R S) (g : R) (b : S →ₐ[R] B)
  (hg : IsUnit (algebraMap R B g))

private abbrev stageAway (i : ApproximationIndex R S) :=
  Localization.Away (algebraMap R (stage h i) g)

private def stageToLocalization (i : ApproximationIndex R S) : stageAway h g i →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (algebraMap R (stage h i) g)
    (f := b.comp (stageToAlgebra h i)) (by simpa only [AlgHom.comp_apply, AlgHom.commutes] using hg)

private theorem stageToLocalization_on_base (i : ApproximationIndex R S) (x : stage h i) :
    stageToLocalization h g b hg i (algebraMap (stage h i) (stageAway h g i) x) =
      b (stageToAlgebra h i x) :=
  IsLocalization.Away.lift_eq (g := (b.comp (stageToAlgebra h i)).toRingHom)
    (algebraMap R (stage h i) g)
    (by
      change IsUnit ((b.comp (stageToAlgebra h i)) (algebraMap R (stage h i) g))
      rw [AlgHom.commutes]
      exact hg) x

private theorem stageLocalization_exists_surjective [Algebra.FinitePresentation R B]
    (hfrac : ∀ x : B, ∃ (n : ℕ) (s : S), b s = (algebraMap R B g) ^ n * x)
    (i : ApproximationIndex R S) :
    ∃ j : ApproximationIndex R S, i ≤ j ∧
      Function.Surjective (stageToLocalization h g b hg j) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R B).out
  choose n t ht using fun x : s => hfrac x.1
  let j : ApproximationIndex R S := ⟨(i.1.1 ∪ Finset.univ.image t, i.1.2), by
    intro q hq
    exact ⟨(i.2 q hq).1.trans Finset.subset_union_left, (i.2 q hq).2⟩⟩
  refine ⟨j, ⟨Finset.subset_union_left, le_rfl⟩, (AlgHom.range_eq_top _).mp ?_⟩
  apply top_unique
  rw [← hs]
  apply Algebra.adjoin_le
  intro x hx
  let x' : ↥s := ⟨x, hx⟩
  let v : Var j := ⟨t x', Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ x'))⟩
  let a := algebraMap R (stage h j) g
  let A := stageAway h g j
  let f := stageToLocalization h g b hg j
  let w := algebraMap (stage h j) A (stageQuotient h j (MvPolynomial.X v))
  let u := (IsLocalization.Away.algebraMap_pow_isUnit (S := A) a (n x')).unit
  refine ⟨↑u⁻¹ * w, ?_⟩
  have hu : (u : A) = (algebraMap R A g) ^ n x' := by
    change (algebraMap (stage h j) A a) ^ _ = _
    rw [← IsScalarTower.algebraMap_apply]
  have hw : f w = b (t x') := by
    rw [stageToLocalization_on_base]
    change b (MvPolynomial.aeval (R := R) (Subtype.val : Var j → S) (MvPolynomial.X v)) = _
    rw [MvPolynomial.aeval_X]
  have hu' : f (u : A) = (algebraMap R B g) ^ n x' := by
    rw [hu, map_pow, f.commutes]
  apply (hg.pow (n x')).mul_left_cancel
  calc
    (algebraMap R B g) ^ n x' * f (↑u⁻¹ * w) =
        f ((u : A) * (↑u⁻¹ * w)) := by
      rw [← hu']
      exact (f.map_mul _ _).symm
    _ = f w := congrArg f (by rw [← mul_assoc, Units.mul_inv, one_mul])
    _ = b (t x') := hw
    _ = (algebraMap R B g) ^ n x' * x := ht x'

private theorem stageLocalization_exists_bijective [Algebra.FinitePresentation R B]
    (hb : Function.Injective b)
    (hfrac : ∀ x : B, ∃ (n : ℕ) (s : S), b s = (algebraMap R B g) ^ n * x)
    (i : ApproximationIndex R S) :
    ∃ j : ApproximationIndex R S, i ≤ j ∧
      Function.Bijective (stageToLocalization h g b hg j) := by
  classical
  obtain ⟨k, hik, hsurj⟩ := stageLocalization_exists_surjective h g b hg hfrac i
  let A := stageAway h g k
  let a := algebraMap R (stage h k) g
  let f := stageToLocalization h g b hg k
  let : Algebra.FinitePresentation R (stage h k) := (stage_finite h k).2
  let : Algebra.FinitePresentation (stage h k) A := IsLocalization.Away.finitePresentation a
  let : Algebra.FinitePresentation R A := Algebra.FinitePresentation.trans R (stage h k) A
  obtain ⟨s, hs⟩ := Algebra.FinitePresentation.ker_fG_of_surjective f hsurj
  choose n y hy using fun z : s => IsLocalization.Away.surj a (z.1 : A)
  choose q hq using fun z : s =>
    (Ideal.Quotient.mk_surjective (I := Ideal.span (relations h k))) (y z)
  have hzero (z : s) : MvPolynomial.aeval (R := R) (Subtype.val : Var k → S) (q z) = 0 := by
    have hz : f (z : A) = 0 := RingHom.mem_ker.mp (hs ▸ Ideal.subset_span z.2)
    have he := congrArg f (hy z)
    rw [map_mul, hz, zero_mul, stageToLocalization_on_base, ← hq z] at he
    apply hb
    rw [map_zero]
    exact he.symm
  obtain ⟨j, hkj, hsurj', hkill⟩ := stageCanKill h k (Finset.univ.image q) (by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
    exact hzero z)
  let a' := algebraMap R (stage h j) g
  let A' := stageAway h g j
  let f' := stageToLocalization h g b hg j
  have hbase : stageMap h hkj a = a' := (stageMap h hkj).commutes g
  let : IsLocalization.Away (stageMap h hkj a) A' := hbase.symm ▸
    (inferInstance : IsLocalization.Away a' A')
  let m := IsLocalization.Away.mapₐ A A' (stageMap h hkj) a
  have hm : Function.Surjective m :=
    IsLocalization.Away.mapₐ_surjective_of_surjective a hsurj'
  have hf : f'.comp m = f := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    apply RingHom.ext
    intro x
    change f' (m (algebraMap (stage h k) A x)) = f (algebraMap (stage h k) A x)
    rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq,
      stageToLocalization_on_base, stageToLocalization_on_base]
    congr 1
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    change stageToAlgebra h j (stageMap h hkj (stageQuotient h k v)) =
      stageToAlgebra h k (stageQuotient h k v)
    rw [stageMap_quotient]
    exact MvPolynomial.aeval_rename _ _ _
  have hk : RingHom.ker f.toRingHom ≤ RingHom.ker m.toRingHom := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro z hz
    let z' : ↥s := ⟨z, hz⟩
    have hz' := congrArg m (hy z')
    have hx : m (algebraMap (stage h k) A (y z')) = 0 := by
      rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq, ← hq z']
      change algebraMap (stage h j) A' (stageMap h hkj (stageQuotient h k (q z'))) = 0
      rw [hkill _ (Finset.mem_image_of_mem q (Finset.mem_univ z')), map_zero]
    change m (z * algebraMap (stage h k) A a ^ n z') = m (algebraMap (stage h k) A (y z')) at hz'
    rw [map_mul, hx] at hz'
    apply RingHom.mem_ker.mpr
    have hu := (IsLocalization.Away.algebraMap_pow_isUnit (S := A) a (n z')).map m
    exact hu.mul_right_cancel (hz'.trans (zero_mul _).symm)
  refine ⟨j, hik.trans hkj, ?_, ?_⟩
  · apply (injective_iff_map_eq_zero f').mpr
    intro z hz
    obtain ⟨x, rfl⟩ := hm z
    apply hk
    change f x = 0
    rw [← hf]
    exact hz
  · intro z
    obtain ⟨x, rfl⟩ := hsurj z
    exact ⟨m x, AlgHom.congr_fun hf x⟩

include h in
/-- Theorem 10.11 のための有限表示有限近似。局所化の有限表示性により、
各段の主局所化を指定された環と同型にできる。 -/
theorem integral_isFilteredColimit_finitePresentation_fixedLocalization
    [Algebra.FinitePresentation R B] (hb : Function.Injective b)
    (hfrac : ∀ x : B, ∃ (n : ℕ) (s : S), b s = (algebraMap R B g) ^ n * x) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R S)),
      Nonempty (IsColimit (Cocone.mk _ η)) ∧ ∀ i, FinitePresentedFinite R (F.obj i) ∧
        let a := (F.obj i).hom.hom g
        let f := b.toRingHom.comp (η.app i).right.hom
        Function.Bijective (IsLocalization.Away.lift (S := Localization.Away a) a (g := f)
          (by
            have he := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of S => k.hom g)
              (Under.w (η.app i))
            change (η.app i).right.hom a = algebraMap R S g at he
            change IsUnit (b ((η.app i).right.hom a))
            rw [he, b.commutes]
            exact hg)) := by
  classical
  let J := {i : ApproximationIndex R S // Function.Bijective (stageToLocalization h g b hg i)}
  have he (i : ApproximationIndex R S) : ∃ j : J, i ≤ j.1 := by
    obtain ⟨j, hij, hj⟩ := stageLocalization_exists_bijective h g b hg hb hfrac i
    exact ⟨⟨j, hj⟩, hij⟩
  let : Nonempty J := ⟨(he (Classical.arbitrary _)).choose⟩
  let : IsDirectedOrder J := ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    obtain ⟨m, hkm⟩ := he k
    exact ⟨m, hik.trans hkm, hjk.trans hkm⟩⟩
  let mono : Monotone (Subtype.val : J → ApproximationIndex R S) := fun _ _ h => h
  let : mono.functor.Final := mono.final_functor_iff.mpr he
  let c := (approximationCocone h).whisker mono.functor
  have hc := (Functor.Final.isColimitWhiskerEquiv mono.functor _).symm
    (approximationCoconeIsColimit h)
  refine ⟨J, inferInstance, inferInstance, mono.functor ⋙ approximationDiagram h, c.ι, ⟨hc⟩, ?_⟩
  intro i
  constructor
  · change letI := (algebraMap R (stage h i.1)).toAlgebra
      Module.Finite R (stage h i.1) ∧ Algebra.FinitePresentation R (stage h i.1)
    rw [toAlgebra_algebraMap]
    exact stage_finite h i.1
  · exact i.2

end FixedLocalization

end SerrePositivity.BhattScholze.Perfectoidization.Derived



/-!
# 整閉包の局所化を固定した有限近似

## 概要
BS 著者版 Theorem 10.11 の証明で、Lemma 10.12 の層の整閉包を有限表示有限代数で近似する。

## 方針
有限エタールな局所化の各元を、分母を払って整閉包に入れる。局所化を固定できる有限近似を適用する。

## 規約
各近似から整閉包への射と、主局所化から層への指定射を保持する。

## 使われ方
Theorem 10.9 を各近似に適用し、Theorem 10.11 の組み立てに渡す。
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open PerfectoidizationInterface

attribute [local instance] reducedAwayBase

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private theorem reducedAway_algebraMap_isUnit (g : R) :
    IsUnit (algebraMap R (reducedAway R S g) g) :=
  IsLocalization.Away.algebraMap_isUnit (algebraMap R (S ⧸ nilradical S) g)

/-- Theorem 10.11 の g-almost 部分に使う。近似の主局所化は指定した有限エタール層に一致する。 -/
theorem exists_finitePresentation_approximation_fixedLocalization (g : R)
    (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    let T := integralClosureInLocalization R S g
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R T)),
      Nonempty (IsColimit (Cocone.mk _ η)) ∧ ∀ i, FinitePresentedFinite R (F.obj i) ∧
        let a := (F.obj i).hom.hom g
        let f := T.val.toRingHom.comp (η.app i).right.hom
        Function.Bijective (IsLocalization.Away.lift (S := Localization.Away a) a (g := f)
          (by
            have he := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom g)
              (Under.w (η.app i))
            change (η.app i).right.hom a = algebraMap R T g at he
            change IsUnit (T.val ((η.app i).right.hom a))
            rw [he, T.val.commutes]
            exact reducedAway_algebraMap_isUnit R S g)) := by
  let T := integralClosureInLocalization R S g
  let B := reducedAway R S g
  let L := Localization.Away g
  let := GenericEtale.awayAlgebra R (S ⧸ nilradical S) g
  let : IsScalarTower R L B := IsScalarTower.of_algebraMap_eq fun r => by
    change (algebraMap (S ⧸ nilradical S) B) (algebraMap R (S ⧸ nilradical S) r) =
      Localization.awayMap (algebraMap R (S ⧸ nilradical S)) g (algebraMap R L r)
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  let : Module.Finite L B := het.1
  let : Algebra.Etale L B := het.2
  let : Algebra.FinitePresentation R L := IsLocalization.Away.finitePresentation g
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R L B
  have hT : Algebra.IsIntegral R T := T.isIntegral_iff.mpr fun _ h => h
  apply integral_isFilteredColimit_finitePresentation_fixedLocalization hT g T.val
    (reducedAway_algebraMap_isUnit R S g) Subtype.val_injective
  intro x
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Submonoid.powers g) (Rₘ := L) x (IsIntegral.of_finite L x)
  have he : (g ^ n) • x = (algebraMap R B g) ^ n * x := by
    rw [Algebra.smul_def, map_pow]
  refine ⟨n, ⟨(g ^ n) • x, hm⟩, he⟩

end SerrePositivity.BhattScholze.Perfectoidization.Derived
