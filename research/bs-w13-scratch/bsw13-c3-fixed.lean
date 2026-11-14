module

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
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface

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

universe u
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
