module

public import SerrePositivity.CategoryTheory.BoundedHomotopy
public import SerrePositivity.CategoryTheory.FullSubcategoryTriangle
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # 有界ホモトピー圏は項の単一複体から生成される -/

@[expose] public section

universe v u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- 加法圏でも定義できる、下端の項への射。 -/
noncomputable def boundedBottomProjection (K : CochainComplex C ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (K.X i)) :
    K ⟶ (HomologicalComplex.single C (.up ℤ) a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi ↦ (ha i (by
    have : i + 1 = a := hi
    omega)).eq_of_src _ _)

noncomputable instance boundedBottomProjection_f_hasKernel
    (K : CochainComplex C ℤ) (a : ℤ) (ha : ∀ i, i < a → IsZero (K.X i)) (i : ℤ) :
    HasKernel ((boundedBottomProjection K a ha).f i) := by
  by_cases hi : i = a
  · subst i
    have hf : IsIso ((boundedBottomProjection K a ha).f a) := by
      dsimp [boundedBottomProjection]
      rw [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
      infer_instance
    exact ⟨⟨KernelFork.ofι (0 : (0 : C) ⟶ K.X a) (by simp),
      KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance (isZero_zero C)⟩⟩
  · have hf : (boundedBottomProjection K a ha).f i = 0 :=
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) a (K.X a) i hi).eq_of_tgt _ _
    exact ⟨⟨_, KernelFork.IsLimit.ofId _ hf⟩⟩

noncomputable instance boundedBottomProjection_hasKernel
    (K : CochainComplex C ℤ) (a : ℤ) (ha : ∀ i, i < a → IsZero (K.X i)) :
    HasKernel (boundedBottomProjection K a ha) := HomologicalComplex.hasKernel_of_hasKernel_f _

noncomputable instance boundedBottomProjection_eval_preservesKernel
    (K : CochainComplex C ℤ) (a : ℤ) (ha : ∀ i, i < a → IsZero (K.X i)) (i : ℤ) :
    PreservesLimit (parallelPair (boundedBottomProjection K a ha) 0)
      (HomologicalComplex.eval C (.up ℤ) i) :=
  HomologicalComplex.eval_preservesLimit_of_hasKernel_f _ _

omit [HasBinaryBiproducts C] in
lemma boundedBottomKernel_isZero (K : CochainComplex C ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (K.X i)) :
    IsZero ((kernel (boundedBottomProjection K a ha)).X a) := by
  let E := HomologicalComplex.eval C (.up ℤ) a
  have hf : IsIso (E.map (boundedBottomProjection K a ha)) := by
    change IsIso ((boundedBottomProjection K a ha).f a)
    dsimp [boundedBottomProjection]
    rw [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
    infer_instance
  exact (isZero_zero C).of_iso
    (PreservesKernel.iso E (boundedBottomProjection K a ha) ≪≫ kernel.ofMono _)

noncomputable def boundedBottomKernelXIso (K : CochainComplex C ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (K.X i)) (i : ℤ) (hi : i ≠ a) :
    (kernel (boundedBottomProjection K a ha)).X i ≅ K.X i := by
  let E := HomologicalComplex.eval C (.up ℤ) i
  have hf : E.map (boundedBottomProjection K a ha) = 0 :=
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) a (K.X a) i hi).eq_of_tgt _ _
  have := kernel.ι_of_zero hf
  exact PreservesKernel.iso E (boundedBottomProjection K a ha) ≪≫ asIso (kernel.ι _)

noncomputable def boundedBottomSplitting (K : CochainComplex C ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (K.X i)) (i : ℤ) :
    ((ShortComplex.mk (kernel.ι (boundedBottomProjection K a ha))
      (boundedBottomProjection K a ha) (kernel.condition _)).map
        (HomologicalComplex.eval C (.up ℤ) i)).Splitting := by
  by_cases hi : i = a
  · subst i
    refine ShortComplex.Splitting.ofIsZeroOfIsIso _ (boundedBottomKernel_isZero K a ha) ?_
    change IsIso ((boundedBottomProjection K a ha).f a)
    dsimp [boundedBottomProjection]
    rw [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
    infer_instance
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) a (K.X a) i hi)
    let E := HomologicalComplex.eval C (.up ℤ) i
    have hf : E.map (boundedBottomProjection K a ha) = 0 :=
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) a (K.X a) i hi).eq_of_tgt _ _
    have := kernel.ι_of_zero hf
    have he := PreservesKernel.iso_inv_ι E (boundedBottomProjection K a ha)
    have hmap : E.map (kernel.ι (boundedBottomProjection K a ha)) =
        (PreservesKernel.iso E (boundedBottomProjection K a ha)).hom ≫
          kernel.ι (E.map (boundedBottomProjection K a ha)) := by
      rw [← he]; simp
    change IsIso (E.map (kernel.ι (boundedBottomProjection K a ha)))
    rw [hmap]
    infer_instance

omit [HasBinaryBiproducts C] in
/-- 単一複体の共通有界性。 -/
lemma strictlyBoundedComplex_single (X : C) (a : ℤ) :
    strictlyBoundedComplex C ((HomologicalComplex.single C (.up ℤ) a).obj X) :=
  ⟨a, a, inferInstance, inferInstance⟩

/-- 共通有界ホモトピー圏の単一複体。 -/
noncomputable def boundedSingleObj (X : C) (a : ℤ) : BoundedHomotopy C :=
  ⟨(HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) a).obj X),
    (boundedHomotopyProperty_quotient _ _).mpr (strictlyBoundedComplex_single X a)⟩

/-- 任意の次数の単一複体は、次数零の単一複体のシフトである。 -/
noncomputable def boundedSingleShiftIso (X : C) (a : ℤ) :
    (boundedSingleObj X 0)⟦-a⟧ ≅ boundedSingleObj X a := by
  apply ObjectProperty.isoMk
  let i := ((HomotopyCategory.singleFunctors C).shiftIso (-a) a 0 (by omega)).app X
  dsimp only [HomotopyCategory.singleFunctors, SingleFunctors.postcomp, Functor.comp_obj] at i
  exact ((boundedHomotopyInclusion C).commShiftIso (-a)).app (boundedSingleObj X 0) ≪≫ i

/-- 共通有界な複体を有界ホモトピー圏に入れる。 -/
noncomputable abbrev boundedComplexObj (K : CochainComplex C ℤ)
    (hK : strictlyBoundedComplex C K) : BoundedHomotopy C :=
  ⟨(HomotopyCategory.quotient C (.up ℤ)).obj K,
    (boundedHomotopyProperty_quotient _ _).mpr hK⟩

/-- 項の単一複体を含む三角部分圏は、それらの項からなる有界複体を含む。 -/
lemma boundedHomotopy_mem_of_terms
    (P : ObjectProperty (BoundedHomotopy C)) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (p : ObjectProperty C) [p.ContainsZero] [p.IsClosedUnderIsomorphisms]
    (hp : ∀ X, p X → ∀ a : ℤ, P (boundedSingleObj X a))
    (K : CochainComplex C ℤ) (hK : strictlyBoundedComplex C K)
    (ht : ∀ i, p (K.X i)) : P (boundedComplexObj K hK) := by
  obtain ⟨a, b, ha, hb⟩ := hK
  have hbound : ∀ i, (i < a ∨ a + (b - a + 1).toNat ≤ i) → IsZero (K.X i) := by
    intro i hi
    rcases hi with hi | hi
    · exact K.isZero_of_isStrictlyGE a i hi
    · exact K.isZero_of_isStrictlyLE b i (by omega)
  generalize hw : (b - a + 1).toNat = w at hbound
  have hK : strictlyBoundedComplex C K := ⟨a, b, ha, hb⟩
  change P (boundedComplexObj K hK)
  clear hw ha hb b
  induction w generalizing a K with
  | zero =>
      have hz : IsZero K := by
        rw [IsZero.iff_id_eq_zero]
        apply HomologicalComplex.Hom.ext
        funext i
        exact (hbound i (by omega)).eq_of_src _ _
      apply P.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      apply (boundedHomotopyInclusion C).map_injective
      rw [CategoryTheory.Functor.map_id, Functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).mp ((HomotopyCategory.quotient C (.up ℤ)).map_isZero hz)
  | succ w ih =>
      let ha := fun i (hi : i < a) ↦ hbound i (Or.inl hi)
      let π := boundedBottomProjection K a ha
      let L := kernel π
      have hLbound : ∀ i, (i < a + 1 ∨ a + 1 + w ≤ i) → IsZero (L.X i) := by
        intro i hi
        by_cases hia : i = a
        · subst i; exact boundedBottomKernel_isZero K a ha
        · exact (hbound i (by omega)).of_iso (boundedBottomKernelXIso K a ha i hia)
      have hL : strictlyBoundedComplex C L :=
        ⟨a + 1, a + 1 + w, (CochainComplex.isStrictlyGE_iff L (a + 1)).mpr
          (fun i hi ↦ hLbound i (Or.inl hi)), (CochainComplex.isStrictlyLE_iff L (a + 1 + w)).mpr
          (fun i hi ↦ hLbound i (Or.inr hi.le))⟩
      have htL : ∀ i, p (L.X i) := by
        intro i
        by_cases hia : i = a
        · subst i; exact p.prop_of_isZero (boundedBottomKernel_isZero K a ha)
        · exact p.prop_of_iso (boundedBottomKernelXIso K a ha i hia).symm (ht i)
      let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      let T := CochainComplex.trianglehOfDegreewiseSplit S (boundedBottomSplitting K a ha)
      let T' := fullSubcategoryTriangle (boundedHomotopyProperty C) T
        ((boundedHomotopyProperty_quotient _ _).mpr hL)
        ((boundedHomotopyProperty_quotient _ _).mpr hK)
        ((boundedHomotopyProperty_quotient _ _).mpr (strictlyBoundedComplex_single (K.X a) a))
      exact P.ext_of_isTriangulatedClosed₂ T'
        (fullSubcategoryTriangle_distinguished _ _ _ _ _
          (CochainComplex.trianglehOfDegreewiseSplit_distinguished S
            (boundedBottomSplitting K a ha)))
        (ih L htL (a + 1) hLbound hL) (hp (K.X a) (ht a) a)

end SerrePositivity
