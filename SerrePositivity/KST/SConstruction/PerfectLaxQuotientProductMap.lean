module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientCompletionLegs
public import SerrePositivity.KST.SConstruction.TammePerfectProjectionEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceCLeg

/-! # 元の完備化後の二脚の実積射と普遍差の両射影
概要：普遍差の比較関手の値は、元の二脚の実積射と元の両射影の下で可換する。
方針：第一射影の全関手同型と第二射影の厳密等式を、同じ値の BF 表示へ写す。
規約：元の raw 商の二脚と完備化を保持する。使われ方：実積正方形の右辺の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
namespace PerfectLaxQuotient
private lemma perfectProjectionPasting {K : Type*} [Category K]
    {L T P R A B : K} (j : L ⟶ T) (u : T ⟶ R) (v : L ⟶ P) (w : P ⟶ R)
    (a : P ⟶ A) (b : R ⟶ B) (c : T ⟶ B) (e : L ⟶ A) (f : A ⟶ B)
    (hu : u ≫ b = c) (hj : j ≫ c = e ≫ f) (hv : v ≫ a = e)
    (hw : w ≫ b = a ≫ f) : (j ≫ u) ≫ b = (v ≫ w) ≫ b := by
  rw [Category.assoc, hu, hj, Category.assoc, hw, ← Category.assoc, hv]

variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q) (F : perfectStableInfinity.{u} ⟶ Sp.{u})

/-- 元の C・D の値から、元の完備化後の二脚を持つ実 BF 積射。 -/
def productLegMap : Binary.obj
    (perfectInvariantSpectrum F (perfectStableVertex C d.c_complete))
    (perfectInvariantSpectrum F (perfectStableVertex D d.d_complete)) ⟶
    Binary.obj (perfectInvariantSpectrum F d.sequence.rightVertex)
      (perfectInvariantSpectrum F d.sequence.rightVertex) :=
  Binary.lift
    (Binary.fst _ _ ≫ perfectInvariantSpectrumMap F d.cLeg d.c_complete d.right_complete)
    (Binary.snd _ _ ≫ perfectInvariantSpectrumMap F d.dLeg d.d_complete d.right_complete)

/-- 元の実積射の第一射影は、元の完備化後の C 脚。 -/
lemma productLegMap_fst : d.productLegMap F ≫ Binary.fst _ _ =
    Binary.fst _ _ ≫ perfectInvariantSpectrumMap F d.cLeg d.c_complete d.right_complete :=
  Binary.lift_fst _ _

/-- 元の実積射の第二射影は、元の完備化後の D 脚。 -/
lemma productLegMap_snd : d.productLegMap F ≫ Binary.snd _ _ =
    Binary.snd _ _ ≫ perfectInvariantSpectrumMap F d.dLeg d.d_complete d.right_complete :=
  Binary.lift_snd _ _

/-- 同じ普遍差の第一射影の値は、元の C 射影と完備化後の C 脚の合成。 -/
lemma universalLift_value_fst :
    perfectInvariantSpectrumHom F (LaxUniversalDifference.exactLift p q d.sequence.projection)
        d.middle_complete (perfectLaxCategory_isIdempotentComplete
          (𝟙 d.sequence.right) (𝟙 d.sequence.right)
            d.sequence.right_complete d.sequence.right_complete) ≫
      perfectInvariantSpectrumHom F (laxFst (𝟙 d.sequence.right) (𝟙 d.sequence.right))
        (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right) (𝟙 d.sequence.right)
          d.sequence.right_complete d.sequence.right_complete) d.sequence.right_complete =
    perfectInvariantSpectrumHom F (laxFst p q) d.middle_complete d.c_complete ≫
      perfectInvariantSpectrumHom F d.cLeg d.c_complete d.right_complete := by
  let f : laxCategory p q ⟶ d.sequence.right :=
    LaxUniversalDifference.exactLift p q d.sequence.projection ≫
      laxFst (𝟙 d.sequence.right) (𝟙 d.sequence.right)
  let g : laxCategory p q ⟶ d.sequence.right :=
    laxFst p q ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q d.sequence.projection
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom g.hom :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.firstCLegIso p q d.sequence.projection
  have hh := congrArg SpectrumHo.normalize
    (perfectInvariantHoArrow_eq_of_functorIso F d.middle_complete d.sequence.right_complete e)
  have hf := perfectInvariantSpectrumHom_comp F
    (LaxUniversalDifference.exactLift p q d.sequence.projection)
    (laxFst (𝟙 d.sequence.right) (𝟙 d.sequence.right))
    d.middle_complete (perfectLaxCategory_isIdempotentComplete
      (𝟙 d.sequence.right) (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete) d.sequence.right_complete
  have hg := perfectInvariantSpectrumHom_comp F (laxFst p q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q d.sequence.projection)
    d.middle_complete d.c_complete d.sequence.right_complete
  have hm := congrArg (fun a =>
    perfectInvariantSpectrumHom F (laxFst p q) d.middle_complete d.c_complete ≫ a)
      (d.cLeg_projection_value F).symm
  exact hf.symm.trans (hh.trans (hg.trans hm))

/-- 同じ普遍差の第二射影の値は、元の D 射影と完備化後の D 脚の合成。 -/
lemma universalLift_value_snd :
    perfectInvariantSpectrumHom F (LaxUniversalDifference.exactLift p q d.sequence.projection)
        d.middle_complete (perfectLaxCategory_isIdempotentComplete
          (𝟙 d.sequence.right) (𝟙 d.sequence.right)
            d.sequence.right_complete d.sequence.right_complete) ≫
      perfectInvariantSpectrumHom F (laxSnd (𝟙 d.sequence.right) (𝟙 d.sequence.right))
        (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right) (𝟙 d.sequence.right)
          d.sequence.right_complete d.sequence.right_complete) d.sequence.right_complete =
    perfectInvariantSpectrumHom F (laxSnd p q) d.middle_complete d.d_complete ≫
      perfectInvariantSpectrumHom F d.dLeg d.d_complete d.right_complete := by
  let f : laxCategory p q ⟶ d.sequence.right :=
    LaxUniversalDifference.exactLift p q d.sequence.projection ≫
      laxSnd (𝟙 d.sequence.right) (𝟙 d.sequence.right)
  let g : laxCategory p q ⟶ d.sequence.right :=
    laxSnd p q ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q d.sequence.projection
  have he : f.hom = g.hom := by
    change LaxUniversalDifference.lift p q d.sequence.projection ≫
      (laxSnd (𝟙 d.sequence.right) (𝟙 d.sequence.right)).hom =
        (laxSnd p q).hom ≫ (LaxInclusion.fromD p q ≫ d.sequence.projection.hom)
    exact (LaxUniversalDifference.lift_snd p q d.sequence.projection).trans
      (Category.assoc _ _ _)
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom g.hom :=
    eqToIso (congrArg (fun a => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) he)
  have hh := congrArg SpectrumHo.normalize
    (perfectInvariantHoArrow_eq_of_functorIso F d.middle_complete d.sequence.right_complete e)
  have hf := perfectInvariantSpectrumHom_comp F
    (LaxUniversalDifference.exactLift p q d.sequence.projection)
    (laxSnd (𝟙 d.sequence.right) (𝟙 d.sequence.right))
    d.middle_complete (perfectLaxCategory_isIdempotentComplete
      (𝟙 d.sequence.right) (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete) d.sequence.right_complete
  have hg := perfectInvariantSpectrumHom_comp F (laxSnd p q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q d.sequence.projection)
    d.middle_complete d.d_complete d.sequence.right_complete
  have hm := congrArg (fun a =>
    perfectInvariantSpectrumHom F (laxSnd p q) d.middle_complete d.d_complete ≫ a)
      (d.dLeg_projection_value F).symm
  exact hf.symm.trans (hh.trans (hg.trans hm))

/-- 同じ実積射の第一射影の類は、元の C 脚の値を回収する。 -/
lemma productLegMap_ho_fst : SpectrumHo.hom (d.productLegMap F) ≫
    SpectrumHo.hom (Binary.fst _ _) = SpectrumHo.hom (Binary.fst _ _) ≫
      perfectInvariantSpectrumHom F d.cLeg d.c_complete d.right_complete := by
  erw [← SpectrumHo.hom_comp, d.productLegMap_fst, SpectrumHo.hom_comp,
    perfectInvariantSpectrumMap_hom]
  rfl

/-- 同じ実積射の第二射影の類は、元の D 脚の値を回収する。 -/
lemma productLegMap_ho_snd : SpectrumHo.hom (d.productLegMap F) ≫
    SpectrumHo.hom (Binary.snd _ _) = SpectrumHo.hom (Binary.snd _ _) ≫
      perfectInvariantSpectrumHom F d.dLeg d.d_complete d.right_complete := by
  erw [← SpectrumHo.hom_comp, d.productLegMap_snd, SpectrumHo.hom_comp,
    perfectInvariantSpectrumMap_hom]
  rfl

variable {F} (hF : IsPerfectLocalizingInvariant F)

/-- 同じ普遍差の比較は、元の両射影同値の下で元の二脚の実積射と可換する。 -/
lemma product_projection_comm :
    perfectInvariantSpectrumHom F (LaxUniversalDifference.exactLift p q d.sequence.projection)
        d.middle_complete (perfectLaxCategory_isIdempotentComplete
          (𝟙 d.sequence.right) (𝟙 d.sequence.right)
            d.sequence.right_complete d.sequence.right_complete) ≫
      (hF.tammePerfectProjectionEquivalence (𝟙 d.sequence.right) (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete).hom =
    (hF.tammePerfectProjectionEquivalence p q d.c_complete d.d_complete).hom ≫
      SpectrumHo.hom (d.productLegMap F) := by
  apply Binary.ho_hom_ext
  · exact perfectProjectionPasting _ _ _ _ _ _ _ _ _
      (hF.tammePerfectProjectionEquivalence_fst (𝟙 d.sequence.right) (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)
      (d.universalLift_value_fst F)
      (hF.tammePerfectProjectionEquivalence_fst p q d.c_complete d.d_complete)
      (d.productLegMap_ho_fst F)
  · exact perfectProjectionPasting _ _ _ _ _ _ _ _ _
      (hF.tammePerfectProjectionEquivalence_snd (𝟙 d.sequence.right) (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)
      (d.universalLift_value_snd F)
      (hF.tammePerfectProjectionEquivalence_snd p q d.c_complete d.d_complete)
      (d.productLegMap_ho_snd F)

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
