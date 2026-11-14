module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.RingTheory.FinitePresentation
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
    let s := MvPolynomial.rename (Subtype.val : Var i → S) (q - r)
    have hs : s.vars ⊆ i.1.1 := by
      intro v hv
      obtain ⟨w, hw⟩ := MvPolynomial.mem_vars_rename _ _ hv
      exact hw.2 ▸ w.property
    have hz : MvPolynomial.aeval (R := R) (id : S → S) s = 0 := by
      change MvPolynomial.aeval (R := R) (Subtype.val : Var i → S) q =
        MvPolynomial.aeval (R := R) (Subtype.val : Var i → S) r at he
      rw [MvPolynomial.aeval_rename, map_sub, sub_eq_zero]
      exact he
    let j : ApproximationIndex R S := ⟨(i.1.1, insert s i.1.2), by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨hs, hz⟩
      · exact i.2 t ht⟩
    let hij : i ≤ j := ⟨le_rfl, fun _ hv => Finset.mem_insert_of_mem hv⟩
    refine ⟨j, homOfLE hij, ?_⟩
    change stageMap h hij (stageQuotient h i q) = stageMap h hij (stageQuotient h i r)
    rw [← sub_eq_zero, ← map_sub, ← map_sub, stageMap_quotient]
    let sj : {t // t ∈ j.1.2} := ⟨s, Finset.mem_insert_self _ _⟩
    have heq : MvPolynomial.rename (varInclusion hij) (q - r) = restrictRelation j sj := by
      apply MvPolynomial.rename_injective (Subtype.val : Var j → S) Subtype.val_injective
      rw [MvPolynomial.rename_rename, rename_restrictRelation j]
      rfl
    rw [heq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨sj, rfl⟩))

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

end SerrePositivity.BhattScholze.Perfectoidization.Derived
