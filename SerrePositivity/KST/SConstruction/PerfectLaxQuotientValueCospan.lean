module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductEdgeClasses

/-! # 元の C・D 射対と完備化後の二脚の実 BF 値
概要：元の完全関手の同じ BF 表示を使い、射対の実積包含と二脚の可換性を与える。
方針：既存の正規化した射の類の合成則・全関手同型を、元の実 BF 射で表す。
規約：元の射のクラスを保持する。使われ方：四辺固定の実正方形と pullback 錐。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q) (F : perfectStableInfinity.{u} ⟶ Sp.{u})

/-- 元の左端から C への、同じ値の実 BF 射。 -/
def valueCSource := perfectInvariantSpectrumMap F d.cSource d.left_complete d.c_complete

/-- 元の左端から D への、同じ値の実 BF 射。 -/
def valueDSource := perfectInvariantSpectrumMap F d.dSource d.left_complete d.d_complete

/-- 元の raw 商の C 脚を完備化した、同じ値の実 BF 射。 -/
def valueCLeg := perfectInvariantSpectrumMap F d.cLeg d.c_complete d.right_complete

/-- 元の raw 商の D 脚を完備化した、同じ値の実 BF 射。 -/
def valueDLeg := perfectInvariantSpectrumMap F d.dLeg d.d_complete d.right_complete

/-- 元の C・D への射対そのものを持つ、実 BF 積への包含。 -/
def valueProductInclusion := Binary.lift (d.valueCSource F) (d.valueDSource F)

/-- 同じ実積包含の第一射影は、元の C への射の値の類。 -/
lemma valueProductInclusion_ho_fst : SpectrumHo.hom (d.valueProductInclusion F) ≫
    SpectrumHo.hom (Binary.fst _ _) =
      perfectInvariantSpectrumHom F d.cSource d.left_complete d.c_complete := by
  erw [← SpectrumHo.hom_comp, valueProductInclusion, Binary.lift_fst,
    valueCSource, perfectInvariantSpectrumMap_hom]

/-- 同じ実積包含の第二射影は、元の D への射の値の類。 -/
lemma valueProductInclusion_ho_snd : SpectrumHo.hom (d.valueProductInclusion F) ≫
    SpectrumHo.hom (Binary.snd _ _) =
      perfectInvariantSpectrumHom F d.dSource d.left_complete d.d_complete := by
  erw [← SpectrumHo.hom_comp, valueProductInclusion, Binary.lift_snd,
    valueDSource, perfectInvariantSpectrumMap_hom]

/-- 元の同じ二脚は、実 BF 値の h Sp 内で可換する。 -/
lemma valueCospan_comm : SpectrumHo.hom (d.valueCSource F) ≫
    SpectrumHo.hom (d.valueCLeg F) = SpectrumHo.hom (d.valueDSource F) ≫
      SpectrumHo.hom (d.valueDLeg F) := by
  have he := congrArg SpectrumHo.normalize (d.value_legs_comm F)
  have hc := SpectrumHo.normalize_comp
    (perfectInvariantHoArrow F d.cSource d.left_complete d.c_complete)
    (perfectInvariantHoArrow F d.cLeg d.c_complete d.right_complete)
  have hd := SpectrumHo.normalize_comp
    (perfectInvariantHoArrow F d.dSource d.left_complete d.d_complete)
    (perfectInvariantHoArrow F d.dLeg d.d_complete d.right_complete)
  have hn := hc.symm.trans (he.trans hd)
  erw [valueCSource, valueCLeg, valueDSource, valueDLeg,
    perfectInvariantSpectrumMap_hom, perfectInvariantSpectrumMap_hom,
    perfectInvariantSpectrumMap_hom, perfectInvariantSpectrumMap_hom]
  exact hn

/-- 元の普遍差の核の射の同じ BF 値。 -/
def valueKernelMap := perfectInvariantSpectrumMap F
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion d.sequence.projection)
    d.left_complete d.sequence.right_complete

variable {F} (hF : IsPerfectLocalizingInvariant F)

/-- 下辺の元の包含と両射影の組は、元の C・D 射対の実 BF 積包含そのものの類。 -/
lemma valueProductInclusion_projection :
    perfectInvariantSpectrumHom F d.inclusion d.left_complete d.middle_complete ≫
      (hF.tammePerfectProjectionEquivalence p q d.c_complete d.d_complete).hom =
    SpectrumHo.hom (d.valueProductInclusion F) := by
  apply Binary.ho_hom_ext
  · have he := congrArg (fun a =>
      perfectInvariantSpectrumHom F d.inclusion d.left_complete d.middle_complete ≫ a)
        (hF.tammePerfectProjectionEquivalence_fst p q d.c_complete d.d_complete)
    have hc := perfectInvariantSpectrumHom_comp F d.inclusion (laxFst p q)
      d.left_complete d.middle_complete d.c_complete
    exact (Category.assoc _ _ _).trans
      (he.trans (hc.symm.trans (d.valueProductInclusion_ho_fst F).symm))
  · have he := congrArg (fun a =>
      perfectInvariantSpectrumHom F d.inclusion d.left_complete d.middle_complete ≫ a)
        (hF.tammePerfectProjectionEquivalence_snd p q d.c_complete d.d_complete)
    have hc := perfectInvariantSpectrumHom_comp F d.inclusion (laxSnd p q)
      d.left_complete d.middle_complete d.d_complete
    exact (Category.assoc _ _ _).trans
      (he.trans (hc.symm.trans (d.valueProductInclusion_ho_snd F).symm))

/-- 同じ移送正方形の下辺は、元の実 C・D 射対の包含を回収する。 -/
lemma productSquare_bottom_native_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (d.productSquare hF)) =
    Arrow.mk (SpectrumHo.hom (d.valueProductInclusion F)) :=
  (d.productSquare_bottom_arrow hF).trans
    (congrArg Arrow.mk (d.valueProductInclusion_projection hF))

/-- 同じ移送正方形の左辺は、元の核の射の実 BF 表示の類。 -/
lemma productSquare_left_native_arrow : Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoLeft (d.productSquare hF)) =
    Arrow.mk (SpectrumHo.hom (d.valueKernelMap F)) :=
  (d.productSquare_left_arrow hF).trans (congrArg Arrow.mk
    (perfectInvariantSpectrumMap_hom F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion d.sequence.projection)
        d.left_complete d.sequence.right_complete).symm)

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
