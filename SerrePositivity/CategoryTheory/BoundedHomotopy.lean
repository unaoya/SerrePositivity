module

public import SerrePositivity.CategoryTheory.HomotopyProperty
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation

/-! # 有界ホモトピー圏

## 概要

共通の有限次数範囲をもつ複体のホモトピー圏（有界ホモトピー圏）と、それが項の単一複体から生成されること、項ごとの切り詰めの完全三角形を与える。

## 方針

有界性は `IsStrictlyGE`・`IsStrictlyLE` で書く。生成は次数の幅についての帰納法で、項ごとの切り詰めの三角形を使う。

## 規約

項ごとの切り詰めは今 HomologicalAlgebra/StupidTruncation を使う。最新の Mathlib の `stupidTrunc` への置き換えは Mathlib を上げるまで保留（計画 H）。

## 使われ方

PerfectComplex の有限射影複体、Asymptotic の列の複体。
-/

@[expose] public noncomputable section

universe v u v' u'

section BoundedHomotopyPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- ある有限な次数範囲の外で項が零となる複体の条件。 -/
def strictlyBoundedComplex : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- Integer shifts translate a strict finite degree range. -/
lemma strictlyBoundedComplex_shift {K : CochainComplex C ℤ}
    (hK : strictlyBoundedComplex C K) (n : ℤ) : strictlyBoundedComplex C (K⟦n⟧) := by
  obtain ⟨a, b, ha, hb⟩ := hK
  exact ⟨a - n, b - n, K.isStrictlyGE_shift a n _ (by omega),
    K.isStrictlyLE_shift b n _ (by omega)⟩

/-- 有界な代表複体をもつホモトピー圏の対象の条件。 -/
def boundedHomotopyProperty : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (strictlyBoundedComplex C).strictMap (HomotopyCategory.quotient _ _)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- 商関手の像における有界性は、元の複体の厳密な有界性である。 -/
@[simp] lemma boundedHomotopyProperty_quotient (K : CochainComplex C ℤ) :
    boundedHomotopyProperty C ((HomotopyCategory.quotient _ _).obj K) ↔
      strictlyBoundedComplex C K :=
  homotopyProperty_strictMap_quotient (strictlyBoundedComplex C) K

instance : (boundedHomotopyProperty C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0,
      Functor.map_isZero _ (isZero_zero _), by
        rw [boundedHomotopyProperty_quotient]
        exact ⟨0, 0, inferInstance, inferInstance⟩⟩

instance : (boundedHomotopyProperty C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        rw [boundedHomotopyProperty_quotient] at hK
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          boundedHomotopyProperty_quotient]
        exact strictlyBoundedComplex_shift C hK n }

omit [HasZeroObject C] in
/-- 二つの有界複体の射の錐も、明示的な共通次数範囲をもつ。 -/
lemma strictlyBoundedComplex_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : strictlyBoundedComplex C K) (hL : strictlyBoundedComplex C L) :
    strictlyBoundedComplex C (CochainComplex.mappingCone f) := by
  obtain ⟨a, b, ha, hb⟩ := hK
  obtain ⟨c, d, hc, hd⟩ := hL
  refine ⟨min (a - 1) c, max b d, ?_, ?_⟩
  · exact CochainComplex.isStrictlyGE_mappingCone f a c _ (by omega) (by omega)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    simp only [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyLE b _ (by omega),
      L.isZero_of_isStrictlyLE d _ (by omega)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (boundedHomotopyProperty C).IsTriangulatedClosed₃ :=
  homotopyProperty_isTriangulatedClosed₃ _ _ (boundedHomotopyProperty_quotient C)
    (fun f => strictlyBoundedComplex_mappingCone C f)

instance : (boundedHomotopyProperty C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- 共通の有限次数範囲をもつ複体のホモトピー圏。 -/
abbrev BoundedHomotopy := (boundedHomotopyProperty C).FullSubcategory

/-- 有界ホモトピー圏から全ホモトピー圏への完全忠実な三角関手。 -/
abbrev boundedHomotopyInclusion : BoundedHomotopy C ⥤ HomotopyCategory C (.up ℤ) :=
  (boundedHomotopyProperty C).ι

variable {C} {D : Type*} [Category* D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 加法関手は共通有界な複体のホモトピー圏の関手を誘導する。 -/
@[implicit_reducible]
def mapBoundedHomotopy : BoundedHomotopy C ⥤ BoundedHomotopy D :=
  (boundedHomotopyProperty D).lift
    (boundedHomotopyInclusion C ⋙ F.mapHomotopyCategory (.up ℤ)) (by
      rintro ⟨X, hX⟩
      obtain ⟨K, rfl⟩ := X.quotient_obj_surjective
      dsimp
      simp only [boundedHomotopyProperty_quotient, strictlyBoundedComplex] at hX ⊢
      obtain ⟨a, b, ha, hb⟩ := hX
      exact ⟨a, b,
        inferInstanceAs (CochainComplex.IsStrictlyGE
          ((F.mapHomologicalComplex (.up ℤ)).obj K) a),
        inferInstanceAs (CochainComplex.IsStrictlyLE
          ((F.mapHomologicalComplex (.up ℤ)).obj K) b)⟩)

noncomputable instance : (mapBoundedHomotopy F).CommShift ℤ :=
  inferInstanceAs (((boundedHomotopyProperty D).lift
    (boundedHomotopyInclusion C ⋙ F.mapHomotopyCategory (.up ℤ)) _).CommShift ℤ)

instance : (mapBoundedHomotopy F).IsTriangulated := by
  dsimp only [mapBoundedHomotopy]
  infer_instance

end SerrePositivity

end BoundedHomotopyPart

section BoundedHomotopyGenerationPart

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

end BoundedHomotopyGenerationPart

section TruncationTrianglePart

namespace SerrePositivity.StupidTruncation

open CategoryTheory Limits Pretriangulated

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

omit [HasBinaryBiproducts C] in
lemma above_bounded (K : CochainComplex C ℤ) (hK : strictlyBoundedComplex C K) (a : ℤ) :
    strictlyBoundedComplex C (above K a) := by
  obtain ⟨b, c, hb, hc⟩ := hK
  exact ⟨b, c, inferInstance, inferInstance⟩

omit [HasBinaryBiproducts C] in
lemma below_bounded (K : CochainComplex C ℤ) (hK : strictlyBoundedComplex C K) (b : ℤ) :
    strictlyBoundedComplex C (below K b) := by
  obtain ⟨a, c, ha, hc⟩ := hK
  exact ⟨a, c, inferInstance, inferInstance⟩

/-- 切り詰めの包含を有界ホモトピー圏で見る。 -/
noncomputable def boundedInclusion (K : CochainComplex C ℤ)
    (hK : strictlyBoundedComplex C K) (a : ℤ) :
    boundedComplexObj (above K a) (above_bounded K hK a) ⟶ boundedComplexObj K hK :=
  ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (inclusion K a))

/-- 切り詰めとその尾部を結ぶ、有界ホモトピー圏の完全三角形。 -/
noncomputable def boundedTriangle (K : CochainComplex C ℤ)
    (hK : strictlyBoundedComplex C K) (a : ℤ) : Triangle (BoundedHomotopy C) :=
  fullSubcategoryTriangle (boundedHomotopyProperty C)
    (CochainComplex.trianglehOfDegreewiseSplit (shortComplex K a) (splitting K a))
    ((boundedHomotopyProperty_quotient _ _).mpr (above_bounded K hK a))
    ((boundedHomotopyProperty_quotient _ _).mpr hK)
    ((boundedHomotopyProperty_quotient _ _).mpr (below_bounded K hK (a - 1)))

lemma boundedTriangle_distinguished (K : CochainComplex C ℤ)
    (hK : strictlyBoundedComplex C K) (a : ℤ) :
    boundedTriangle K hK a ∈ distTriang (BoundedHomotopy C) :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished (shortComplex K a) (splitting K a))

/-- 尾部を零に送る三角関手は、切り詰めの包含を同型に送る。 -/
lemma isIso_map_boundedInclusion
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : BoundedHomotopy C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (K : CochainComplex C ℤ) (hK : strictlyBoundedComplex C K) (a : ℤ)
    (hz : IsZero (T.obj (boundedComplexObj (below K (a - 1))
      (below_bounded K hK (a - 1))))) : IsIso (T.map (boundedInclusion K hK a)) :=
  (Triangle.isZero₃_iff_isIso₁ _ (T.map_distinguished _
    (boundedTriangle_distinguished K hK a))).mp hz

end SerrePositivity.StupidTruncation

end TruncationTrianglePart
