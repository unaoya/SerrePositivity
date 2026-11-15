module


public meta import SerrePositivity.Util.Citation
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
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingInterface

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
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Theorem 10.11 の有限表示有限 R 代数の条件。 -/
def _root_.SerrePositivity.CommutativeAlgebra.FinitePresentedFinite (U : A_R R) : Prop :=
  letI := U.hom.hom.toAlgebra
  Module.Finite R U.right ∧ Algebra.FinitePresentation R U.right

private def _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex :=
  { i : Finset S × Finset (MvPolynomial S R) //
    ∀ q ∈ i.2, q.vars ⊆ i.1 ∧ MvPolynomial.aeval (R := R) (id : S → S) q = 0 }

private instance : Preorder (_root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) := inferInstanceAs
  (Preorder { _i : Finset S × Finset (MvPolynomial S R) // _ })

private instance : Nonempty (_root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :=
  ⟨⟨(∅, ∅), by intro q hq; exact (Finset.notMem_empty q hq).elim⟩⟩

private instance : IsDirectedOrder (_root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) where
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

private abbrev _root_.SerrePositivity.CommutativeAlgebra.Var (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) := {x // x ∈ i.1.1}
private abbrev _root_.SerrePositivity.CommutativeAlgebra.StagePolynomial (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) := MvPolynomial (_root_.SerrePositivity.CommutativeAlgebra.Var i) R

private def _root_.SerrePositivity.CommutativeAlgebra.restrictRelation (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) (q : {q // q ∈ i.1.2}) :
    _root_.SerrePositivity.CommutativeAlgebra.StagePolynomial i :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range q.1 (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S)
    Subtype.val_injective (by simpa using (i.2 q.1 q.2).1)).choose

private theorem _root_.SerrePositivity.CommutativeAlgebra.rename_restrictRelation (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) (q : {q // q ∈ i.1.2}) :
    MvPolynomial.rename (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S) (_root_.SerrePositivity.CommutativeAlgebra.restrictRelation i q) = q :=
  (MvPolynomial.exists_rename_eq_of_vars_subset_range q.1 (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S)
    Subtype.val_injective (by simpa using (i.2 q.1 q.2).1)).choose_spec

private def _root_.SerrePositivity.CommutativeAlgebra.relations (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    Set (_root_.SerrePositivity.CommutativeAlgebra.StagePolynomial i) :=
  Set.range (_root_.SerrePositivity.CommutativeAlgebra.restrictRelation i) ∪
    Set.range (fun x : _root_.SerrePositivity.CommutativeAlgebra.Var i => ((h.isIntegral x.1).choose).toMvPolynomial x)

private def _root_.SerrePositivity.CommutativeAlgebra.stage (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :=
  _root_.SerrePositivity.CommutativeAlgebra.StagePolynomial i ⧸ Ideal.span (_root_.SerrePositivity.CommutativeAlgebra.relations h i)

private instance (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    CommRing (_root_.SerrePositivity.CommutativeAlgebra.stage h i) := inferInstanceAs (CommRing (_ ⧸ _))

private instance (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    Algebra R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) := inferInstanceAs (Algebra R (_ ⧸ _))

private def _root_.SerrePositivity.CommutativeAlgebra.stageQuotient (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    _root_.SerrePositivity.CommutativeAlgebra.StagePolynomial i →ₐ[R] _root_.SerrePositivity.CommutativeAlgebra.stage h i := Ideal.Quotient.mkₐ R _

private def _root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    _root_.SerrePositivity.CommutativeAlgebra.stage h i →ₐ[R] S := by
  apply Ideal.Quotient.liftₐ _ (MvPolynomial.aeval Subtype.val)
  apply (Ideal.span_le.mpr ?_ : Ideal.span (_root_.SerrePositivity.CommutativeAlgebra.relations h i) ≤ RingHom.ker _)
  rintro _ (⟨q, rfl⟩ | ⟨x, rfl⟩)
  · change MvPolynomial.aeval Subtype.val (_root_.SerrePositivity.CommutativeAlgebra.restrictRelation i q) = 0
    rw [← show MvPolynomial.aeval (R := R) (id : S → S)
      (MvPolynomial.rename (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S) (_root_.SerrePositivity.CommutativeAlgebra.restrictRelation i q)) =
        MvPolynomial.aeval Subtype.val (_root_.SerrePositivity.CommutativeAlgebra.restrictRelation i q) from MvPolynomial.aeval_rename _ _ _]
    rw [_root_.SerrePositivity.CommutativeAlgebra.rename_restrictRelation]
    exact (i.2 q.1 q.2).2
  · change MvPolynomial.aeval Subtype.val (((h.isIntegral x.1).choose).toMvPolynomial x) = 0
    rw [MvPolynomial.aeval_toMvPolynomial]
    exact (h.isIntegral x.1).choose_spec.2

private def _root_.SerrePositivity.CommutativeAlgebra.varInclusion {i j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S} (hij : i ≤ j) : _root_.SerrePositivity.CommutativeAlgebra.Var i → _root_.SerrePositivity.CommutativeAlgebra.Var j :=
  fun x => ⟨x.1, hij.1 x.2⟩

private def _root_.SerrePositivity.CommutativeAlgebra.stageMap (h : Algebra.IsIntegral R S) {i j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S} (hij : i ≤ j) :
    _root_.SerrePositivity.CommutativeAlgebra.stage h i →ₐ[R] _root_.SerrePositivity.CommutativeAlgebra.stage h j := by
  let f := (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h j).comp (MvPolynomial.rename (_root_.SerrePositivity.CommutativeAlgebra.varInclusion hij))
  apply Ideal.Quotient.liftₐ _ f
  apply (Ideal.span_le.mpr ?_ : Ideal.span (_root_.SerrePositivity.CommutativeAlgebra.relations h i) ≤ RingHom.ker f.toRingHom)
  rintro _ (⟨q, rfl⟩ | ⟨x, rfl⟩)
  · have he : MvPolynomial.rename (_root_.SerrePositivity.CommutativeAlgebra.varInclusion hij) (_root_.SerrePositivity.CommutativeAlgebra.restrictRelation i q) =
        _root_.SerrePositivity.CommutativeAlgebra.restrictRelation j ⟨q.1, hij.2 q.2⟩ := by
      apply MvPolynomial.rename_injective (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var j → S) Subtype.val_injective
      rw [MvPolynomial.rename_rename, _root_.SerrePositivity.CommutativeAlgebra.rename_restrictRelation j]
      exact _root_.SerrePositivity.CommutativeAlgebra.rename_restrictRelation i q
    change _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h j (MvPolynomial.rename (_root_.SerrePositivity.CommutativeAlgebra.varInclusion hij) (_root_.SerrePositivity.CommutativeAlgebra.restrictRelation i q)) = 0
    rw [he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨_, rfl⟩))
  · change _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h j
      (MvPolynomial.rename (_root_.SerrePositivity.CommutativeAlgebra.varInclusion hij) (((h.isIntegral x.1).choose).toMvPolynomial x)) = 0
    rw [MvPolynomial.rename_toMvPolynomial]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inr ⟨_root_.SerrePositivity.CommutativeAlgebra.varInclusion hij x, rfl⟩))

private theorem _root_.SerrePositivity.CommutativeAlgebra.stageMap_quotient (h : Algebra.IsIntegral R S) {i j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S}
    (hij : i ≤ j) (q : _root_.SerrePositivity.CommutativeAlgebra.StagePolynomial i) :
    _root_.SerrePositivity.CommutativeAlgebra.stageMap h hij (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q) =
      _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h j (MvPolynomial.rename (_root_.SerrePositivity.CommutativeAlgebra.varInclusion hij) q) :=
  rfl

private theorem _root_.SerrePositivity.CommutativeAlgebra.stage_finite (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    Module.Finite R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) ∧ Algebra.FinitePresentation R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) := by
  have hp : Algebra.FinitePresentation R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) :=
    Algebra.FinitePresentation.quotient
      (Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _)))
  let := hp
  suffices hi : Algebra.IsIntegral R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) from ⟨hi.finite, hp⟩
  have hi (x : _root_.SerrePositivity.CommutativeAlgebra.Var i) : IsIntegral R (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i (MvPolynomial.X x)) := by
    refine ⟨(h.isIntegral x.1).choose, (h.isIntegral x.1).choose_spec.1, ?_⟩
    change Polynomial.aeval (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i (MvPolynomial.X x)) (h.isIntegral x.1).choose = 0
    rw [Polynomial.aeval_algHom_apply]
    have hz : _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i (((h.isIntegral x.1).choose).toMvPolynomial x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨x, rfl⟩))
    rwa [Polynomial.toMvPolynomial] at hz
  apply integralClosure_eq_top_iff.mp
  apply top_unique
  have he : Algebra.adjoin R
      (Set.range (fun x : _root_.SerrePositivity.CommutativeAlgebra.Var i => _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i (MvPolynomial.X x))) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    have hmap : MvPolynomial.aeval (fun x : _root_.SerrePositivity.CommutativeAlgebra.Var i => _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i (MvPolynomial.X x)) =
        _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i := (MvPolynomial.aeval_unique _).symm
    rw [hmap]
    exact (AlgHom.range_eq_top _).mpr Ideal.Quotient.mk_surjective
  rw [← he]
  exact Algebra.adjoin_le fun _ ⟨x, hx⟩ => hx ▸ hi x

private def _root_.SerrePositivity.CommutativeAlgebra.stageArrow {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : ofAlgebra R A ⟶ ofAlgebra R B :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (CommRingCat.hom_ext f.comp_algebraMap)

private def _root_.SerrePositivity.CommutativeAlgebra.approximationDiagram (h : Algebra.IsIntegral R S) : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S ⥤ A_R R where
  obj i := ofAlgebra R (_root_.SerrePositivity.CommutativeAlgebra.stage h i)
  map k := _root_.SerrePositivity.CommutativeAlgebra.stageArrow (_root_.SerrePositivity.CommutativeAlgebra.stageMap h (leOfHom k))
  map_id i := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _root_.SerrePositivity.CommutativeAlgebra.stageMap h _ (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q) = _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q
    rw [_root_.SerrePositivity.CommutativeAlgebra.stageMap_quotient]
    exact congrArg (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i) (MvPolynomial.rename_id_apply q)
  map_comp {i j k} f g := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _root_.SerrePositivity.CommutativeAlgebra.stageMap h _ (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q) = _root_.SerrePositivity.CommutativeAlgebra.stageMap h _ (_root_.SerrePositivity.CommutativeAlgebra.stageMap h _ (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q))
    simp only [_root_.SerrePositivity.CommutativeAlgebra.stageMap_quotient, MvPolynomial.rename_rename]
    rfl

private def _root_.SerrePositivity.CommutativeAlgebra.approximationCocone (h : Algebra.IsIntegral R S) : Cocone (_root_.SerrePositivity.CommutativeAlgebra.approximationDiagram h) where
  pt := ofAlgebra R S
  ι :=
    { app := fun i => _root_.SerrePositivity.CommutativeAlgebra.stageArrow (_root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h i)
      naturality := by
        intro i j k
        apply Under.UnderMorphism.ext
        apply CommRingCat.hom_ext
        ext x
        obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
        change _root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h j (_root_.SerrePositivity.CommutativeAlgebra.stageMap h _ (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q)) =
          _root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h i (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q)
        rw [_root_.SerrePositivity.CommutativeAlgebra.stageMap_quotient]
        exact MvPolynomial.aeval_rename _ _ _ }

private theorem _root_.SerrePositivity.CommutativeAlgebra.stageCanKill (h : Algebra.IsIntegral R S) (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S)
    (rels : Finset (_root_.SerrePositivity.CommutativeAlgebra.StagePolynomial i))
    (hrel : ∀ q ∈ rels, MvPolynomial.aeval (R := R) (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S) q = 0) :
    ∃ (j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) (hij : i ≤ j),
      Function.Surjective (_root_.SerrePositivity.CommutativeAlgebra.stageMap h hij) ∧
      ∀ q ∈ rels, _root_.SerrePositivity.CommutativeAlgebra.stageMap h hij (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q) = 0 := by
  classical
  let rename := MvPolynomial.rename (R := R) (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S)
  let j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S := ⟨(i.1.1, i.1.2 ∪ rels.image rename), by
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
    refine ⟨_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q, ?_⟩
    rw [_root_.SerrePositivity.CommutativeAlgebra.stageMap_quotient]
    exact congrArg (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h j) (MvPolynomial.rename_id_apply q)
  · intro q hq
    let sj : {t // t ∈ j.1.2} := ⟨rename q,
      Finset.mem_union_right _ (Finset.mem_image_of_mem rename hq)⟩
    have heq : MvPolynomial.rename (_root_.SerrePositivity.CommutativeAlgebra.varInclusion hij) q = _root_.SerrePositivity.CommutativeAlgebra.restrictRelation j sj := by
      apply MvPolynomial.rename_injective (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var j → S) Subtype.val_injective
      rw [MvPolynomial.rename_rename, _root_.SerrePositivity.CommutativeAlgebra.rename_restrictRelation j]
      rfl
    rw [_root_.SerrePositivity.CommutativeAlgebra.stageMap_quotient, heq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨sj, rfl⟩))

private def _root_.SerrePositivity.CommutativeAlgebra.approximationCoconeIsColimit (h : Algebra.IsIntegral R S) :
    IsColimit (_root_.SerrePositivity.CommutativeAlgebra.approximationCocone h) := by
  classical
  let : IsConnected (_root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) := IsFiltered.isConnected _
  apply isColimitOfReflects (Under.forget (CommRingCat.of R))
  let : ReflectsColimit (_root_.SerrePositivity.CommutativeAlgebra.approximationDiagram h ⋙ Under.forget (CommRingCat.of R))
      (forget CommRingCat) := reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    let i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S := ⟨({x}, ∅), by simp⟩
    refine ⟨i, _root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i (MvPolynomial.X ⟨x, Finset.mem_singleton_self _⟩), ?_⟩
    change x = MvPolynomial.aeval (R := R) (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S)
      (MvPolynomial.X ⟨x, _⟩)
    simp
  · intro i x y he
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    change MvPolynomial.aeval (R := R) (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S) q =
      MvPolynomial.aeval (R := R) (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var i → S) r at he
    obtain ⟨j, hij, _, hz⟩ := _root_.SerrePositivity.CommutativeAlgebra.stageCanKill h i {q - r} (by
      intro t ht
      obtain rfl := Finset.mem_singleton.mp ht
      simpa only [map_sub, sub_eq_zero] using he)
    refine ⟨j, homOfLE hij, ?_⟩
    change _root_.SerrePositivity.CommutativeAlgebra.stageMap h hij (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i q) = _root_.SerrePositivity.CommutativeAlgebra.stageMap h hij (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h i r)
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact hz _ (Finset.mem_singleton_self _)

/-- Theorem 10.11 の有限表示有限への帰着。整代数は有限表示有限代数の filtered 余極限である。 -/
theorem _root_.SerrePositivity.CommutativeAlgebra.integral_isFilteredColimit_finitePresentation (h : Algebra.IsIntegral R S) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R S)),
      (∀ i, _root_.SerrePositivity.CommutativeAlgebra.FinitePresentedFinite R (F.obj i)) ∧ Nonempty (IsColimit (Cocone.mk _ η)) := by
  refine ⟨_root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S, inferInstance, inferInstance, _root_.SerrePositivity.CommutativeAlgebra.approximationDiagram h,
    (_root_.SerrePositivity.CommutativeAlgebra.approximationCocone h).ι, ?_, ⟨_root_.SerrePositivity.CommutativeAlgebra.approximationCoconeIsColimit h⟩⟩
  intro i
  change letI := (algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h i)).toAlgebra
    Module.Finite R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) ∧ Algebra.FinitePresentation R (_root_.SerrePositivity.CommutativeAlgebra.stage h i)
  rw [toAlgebra_algebraMap]
  exact _root_.SerrePositivity.CommutativeAlgebra.stage_finite h i

section FixedLocalization

variable {B : Type u} [CommRing B] [Algebra R B]
  (h : Algebra.IsIntegral R S) (g : R) (b : S →ₐ[R] B)
  (hg : IsUnit (algebraMap R B g))

private abbrev _root_.SerrePositivity.CommutativeAlgebra.stageAway (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :=
  Localization.Away (algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) g)

private def _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) : _root_.SerrePositivity.CommutativeAlgebra.stageAway h g i →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) g)
    (f := b.comp (_root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h i)) (by simpa only [AlgHom.comp_apply, AlgHom.commutes] using hg)

private theorem _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization_on_base (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) (x : _root_.SerrePositivity.CommutativeAlgebra.stage h i) :
    _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization h g b hg i (algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h i) (_root_.SerrePositivity.CommutativeAlgebra.stageAway h g i) x) =
      b (_root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h i x) :=
  IsLocalization.Away.lift_eq (g := (b.comp (_root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h i)).toRingHom)
    (algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) g)
    (by
      change IsUnit ((b.comp (_root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h i)) (algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h i) g))
      rw [AlgHom.commutes]
      exact hg) x

private theorem _root_.SerrePositivity.CommutativeAlgebra.stageLocalization_exists_surjective [Algebra.FinitePresentation R B]
    (hfrac : ∀ x : B, ∃ (n : ℕ) (s : S), b s = (algebraMap R B g) ^ n * x)
    (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    ∃ j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S, i ≤ j ∧
      Function.Surjective (_root_.SerrePositivity.CommutativeAlgebra.stageToLocalization h g b hg j) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R B).out
  choose n t ht using fun x : s => hfrac x.1
  let j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S := ⟨(i.1.1 ∪ Finset.univ.image t, i.1.2), by
    intro q hq
    exact ⟨(i.2 q hq).1.trans Finset.subset_union_left, (i.2 q hq).2⟩⟩
  refine ⟨j, ⟨Finset.subset_union_left, le_rfl⟩, (AlgHom.range_eq_top _).mp ?_⟩
  apply top_unique
  rw [← hs]
  apply Algebra.adjoin_le
  intro x hx
  let x' : ↥s := ⟨x, hx⟩
  let v : _root_.SerrePositivity.CommutativeAlgebra.Var j := ⟨t x', Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ x'))⟩
  let a := algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h j) g
  let A := _root_.SerrePositivity.CommutativeAlgebra.stageAway h g j
  let f := _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization h g b hg j
  let w := algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h j) A (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h j (MvPolynomial.X v))
  let u := (IsLocalization.Away.algebraMap_pow_isUnit (S := A) a (n x')).unit
  refine ⟨↑u⁻¹ * w, ?_⟩
  have hu : (u : A) = (algebraMap R A g) ^ n x' := by
    change (algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h j) A a) ^ _ = _
    rw [← IsScalarTower.algebraMap_apply]
  have hw : f w = b (t x') := by
    rw [_root_.SerrePositivity.CommutativeAlgebra.stageToLocalization_on_base]
    change b (MvPolynomial.aeval (R := R) (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var j → S) (MvPolynomial.X v)) = _
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

private theorem _root_.SerrePositivity.CommutativeAlgebra.stageLocalization_exists_bijective [Algebra.FinitePresentation R B]
    (hb : Function.Injective b)
    (hfrac : ∀ x : B, ∃ (n : ℕ) (s : S), b s = (algebraMap R B g) ^ n * x)
    (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) :
    ∃ j : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S, i ≤ j ∧
      Function.Bijective (_root_.SerrePositivity.CommutativeAlgebra.stageToLocalization h g b hg j) := by
  classical
  obtain ⟨k, hik, hsurj⟩ := _root_.SerrePositivity.CommutativeAlgebra.stageLocalization_exists_surjective h g b hg hfrac i
  let A := _root_.SerrePositivity.CommutativeAlgebra.stageAway h g k
  let a := algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h k) g
  let f := _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization h g b hg k
  let : Algebra.FinitePresentation R (_root_.SerrePositivity.CommutativeAlgebra.stage h k) := (_root_.SerrePositivity.CommutativeAlgebra.stage_finite h k).2
  let : Algebra.FinitePresentation (_root_.SerrePositivity.CommutativeAlgebra.stage h k) A := IsLocalization.Away.finitePresentation a
  let : Algebra.FinitePresentation R A := Algebra.FinitePresentation.trans R (_root_.SerrePositivity.CommutativeAlgebra.stage h k) A
  obtain ⟨s, hs⟩ := Algebra.FinitePresentation.ker_fG_of_surjective f hsurj
  choose n y hy using fun z : s => IsLocalization.Away.surj a (z.1 : A)
  choose q hq using fun z : s =>
    (Ideal.Quotient.mk_surjective (I := Ideal.span (_root_.SerrePositivity.CommutativeAlgebra.relations h k))) (y z)
  have hzero (z : s) : MvPolynomial.aeval (R := R) (Subtype.val : _root_.SerrePositivity.CommutativeAlgebra.Var k → S) (q z) = 0 := by
    have hz : f (z : A) = 0 := RingHom.mem_ker.mp (hs ▸ Ideal.subset_span z.2)
    have he := congrArg f (hy z)
    rw [map_mul, hz, zero_mul, _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization_on_base, ← hq z] at he
    apply hb
    rw [map_zero]
    exact he.symm
  obtain ⟨j, hkj, hsurj', hkill⟩ := _root_.SerrePositivity.CommutativeAlgebra.stageCanKill h k (Finset.univ.image q) (by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
    exact hzero z)
  let a' := algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h j) g
  let A' := _root_.SerrePositivity.CommutativeAlgebra.stageAway h g j
  let f' := _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization h g b hg j
  have hbase : _root_.SerrePositivity.CommutativeAlgebra.stageMap h hkj a = a' := (_root_.SerrePositivity.CommutativeAlgebra.stageMap h hkj).commutes g
  let : IsLocalization.Away (_root_.SerrePositivity.CommutativeAlgebra.stageMap h hkj a) A' := hbase.symm ▸
    (inferInstance : IsLocalization.Away a' A')
  let m := IsLocalization.Away.mapₐ A A' (_root_.SerrePositivity.CommutativeAlgebra.stageMap h hkj) a
  have hm : Function.Surjective m :=
    IsLocalization.Away.mapₐ_surjective_of_surjective a hsurj'
  have hf : f'.comp m = f := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    apply RingHom.ext
    intro x
    change f' (m (algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h k) A x)) = f (algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h k) A x)
    rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq,
      _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization_on_base, _root_.SerrePositivity.CommutativeAlgebra.stageToLocalization_on_base]
    congr 1
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h j (_root_.SerrePositivity.CommutativeAlgebra.stageMap h hkj (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h k v)) =
      _root_.SerrePositivity.CommutativeAlgebra.stageToAlgebra h k (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h k v)
    rw [_root_.SerrePositivity.CommutativeAlgebra.stageMap_quotient]
    exact MvPolynomial.aeval_rename _ _ _
  have hk : RingHom.ker f.toRingHom ≤ RingHom.ker m.toRingHom := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro z hz
    let z' : ↥s := ⟨z, hz⟩
    have hz' := congrArg m (hy z')
    have hx : m (algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h k) A (y z')) = 0 := by
      rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq, ← hq z']
      change algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h j) A' (_root_.SerrePositivity.CommutativeAlgebra.stageMap h hkj (_root_.SerrePositivity.CommutativeAlgebra.stageQuotient h k (q z'))) = 0
      rw [hkill _ (Finset.mem_image_of_mem q (Finset.mem_univ z')), map_zero]
    change m (z * algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h k) A a ^ n z') = m (algebraMap (_root_.SerrePositivity.CommutativeAlgebra.stage h k) A (y z')) at hz'
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
theorem _root_.SerrePositivity.CommutativeAlgebra.integral_isFilteredColimit_finitePresentation_fixedLocalization
    [Algebra.FinitePresentation R B] (hb : Function.Injective b)
    (hfrac : ∀ x : B, ∃ (n : ℕ) (s : S), b s = (algebraMap R B g) ^ n * x) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R S)),
      Nonempty (IsColimit (Cocone.mk _ η)) ∧ ∀ i, _root_.SerrePositivity.CommutativeAlgebra.FinitePresentedFinite R (F.obj i) ∧
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
  let J := {i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S // Function.Bijective (_root_.SerrePositivity.CommutativeAlgebra.stageToLocalization h g b hg i)}
  have he (i : _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) : ∃ j : J, i ≤ j.1 := by
    obtain ⟨j, hij, hj⟩ := _root_.SerrePositivity.CommutativeAlgebra.stageLocalization_exists_bijective h g b hg hb hfrac i
    exact ⟨⟨j, hj⟩, hij⟩
  let : Nonempty J := ⟨(he (Classical.arbitrary _)).choose⟩
  let : IsDirectedOrder J := ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    obtain ⟨m, hkm⟩ := he k
    exact ⟨m, hik.trans hkm, hjk.trans hkm⟩⟩
  let mono : Monotone (Subtype.val : J → _root_.SerrePositivity.CommutativeAlgebra.ApproximationIndex R S) := fun _ _ h => h
  let : mono.functor.Final := mono.final_functor_iff.mpr he
  let c := (_root_.SerrePositivity.CommutativeAlgebra.approximationCocone h).whisker mono.functor
  have hc := (Functor.Final.isColimitWhiskerEquiv mono.functor _).symm
    (_root_.SerrePositivity.CommutativeAlgebra.approximationCoconeIsColimit h)
  refine ⟨J, inferInstance, inferInstance, mono.functor ⋙ _root_.SerrePositivity.CommutativeAlgebra.approximationDiagram h, c.ι, ⟨hc⟩, ?_⟩
  intro i
  constructor
  · change letI := (algebraMap R (_root_.SerrePositivity.CommutativeAlgebra.stage h i.1)).toAlgebra
      Module.Finite R (_root_.SerrePositivity.CommutativeAlgebra.stage h i.1) ∧ Algebra.FinitePresentation R (_root_.SerrePositivity.CommutativeAlgebra.stage h i.1)
    rw [toAlgebra_algebraMap]
    exact _root_.SerrePositivity.CommutativeAlgebra.stage_finite h i.1
  · exact i.2

end FixedLocalization

end SerrePositivity.BhattScholze.Perfectoidization.Derived

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 10.11" (partial := component) "filtered 余極限への帰着、有限表示近似、perfectoid の余極限の完備化（BS-W13）。離散性の本体は A6・A7 待ち。E3 の欄は引き続き Inputs ／ 11-10 更新"] _root_.SerrePositivity.CommutativeAlgebra.integral_isFilteredColimit_finitePresentation
