module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationClosedEnvelope
public import SerrePositivity.AlgebraicGeometry.VCoverClosedRestrictionSpecializations
public import SerrePositivity.AlgebraicGeometry.ProperClosedImageSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：v 判定の閉包を有限表示の閉包絡に広げ、平坦な閉部分から fppf 細分を作る。
方針：閉包の特殊化による被覆、固有閉像の全射性、C02 の閉包絡、実際の pullback を使う。
規約：入力の図式をつなぐ Rydh Proposition 3.7 の法則。一般の模型構成自体は別に供給する。
使われ方：A07 の非 Noether 基底の fppf–proper 細分。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 平坦な閉部分の指定開上の被覆を、有限表示の固有全射上の fppf 被覆へ移す。 -/
theorem exists_fppf_closedEnvelope_refinement_of_flat_closedRestriction
    {R : CommRingCat.{u}} {X Y Z : Scheme.{u}}
    (p : Y ⟶ Spec R) [IsProper p] [LocallyOfFinitePresentation p]
    (f : X ⟶ Y) (hf : IsSchemeVCover f) (i : Z ⟶ X) [IsClosedImmersion i]
    [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)] [QuasiCompact (i ≫ f)]
    (U : Y.Opens) (hUc : IsCompact (U : Set Y))
    (hU : ∀ x : X, f x ∈ U → x ∈ Set.range i) (hUp : DenseRange (U.ι ≫ p)) :
    ∃ (T W : Scheme.{u}) (q : W ⟶ T) (r : T ⟶ Spec R) (a : W ⟶ X),
      IsProper r ∧ LocallyOfFinitePresentation r ∧ Surjective r ∧ Flat q ∧
      LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ Surjective q ∧
      a ≫ f ≫ p = q ≫ r := by
  classical
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  letI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  let g := i ≫ f
  let V : Y.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  let K := U.ι.ker
  have hKV : (K.support : Set Y) ⊆ V := by
    rw [Scheme.Hom.support_ker]
    simpa only [Scheme.Opens.range_ι, V, g, TopologicalSpace.Opens.coe_mk] using
      closure_subset_range_comp_of_vCover_closedRestriction f hf i U hUc hU
  obtain ⟨J, hJK, hJfp, hJV⟩ := exists_finitePresentation_closedEnvelope K V hKV
  letI : LocallyOfFinitePresentation J.subschemeι := hJfp
  let r := J.subschemeι ≫ p
  have hKsurj : Surjective (K.subschemeι ≫ p) :=
    surjective_imageι_comp_of_denseRange U.ι p hUp
  let k : K.subscheme ⟶ J.subscheme := Scheme.IdealSheafData.inclusion hJK
  have hfactor : k ≫ r = K.subschemeι ≫ p := by
    dsimp [k, r]
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have hrsurj : Surjective r := by
    constructor
    intro s
    obtain ⟨z, hz⟩ := hKsurj.surj s
    exact ⟨k z, by change (k ≫ r) z = s; rw [hfactor]; exact hz⟩
  let q := pullback.snd g J.subschemeι
  have hqsurj : Surjective q := by
    constructor
    intro t
    have ht : J.subschemeι t ∈ J.support := by
      exact (Set.ext_iff.mp J.range_subschemeι (J.subschemeι t)).mp ⟨t, rfl⟩
    obtain ⟨z, hz⟩ := hJV ht
    obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback z t hz
    exact ⟨w, hw⟩
  refine ⟨J.subscheme, pullback g J.subschemeι, q, r, pullback.fst g J.subschemeι ≫ i,
    inferInstance, inferInstance, hrsurj, inferInstance, inferInstance, inferInstance, hqsurj, ?_⟩
  change (pullback.fst g J.subschemeι ≫ i) ≫ f ≫ p =
    pullback.snd g J.subschemeι ≫ J.subschemeι ≫ p
  rw [Category.assoc, ← Category.assoc i f p]
  change pullback.fst g J.subschemeι ≫ g ≫ p = _
  rw [← Category.assoc, pullback.condition, Category.assoc]

end SerrePositivity.AlgebraicGeometry
