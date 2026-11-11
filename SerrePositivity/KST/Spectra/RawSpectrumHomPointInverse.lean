module

public import SerrePositivity.KST.Spectra.RawSpectrumHomPoints

/-!
概要：元の全 Hom の点つき単位パラメータを、同じ各段を持つ厳密な列射へ戻す。
方針：各段を uncurry' し、元の整合条件を curry' の単射性で構造条件へ戻す。
規約：標的は任意の Kan 列。使われ方：指定した全パラメータ部分の相対厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の単位パラメータの厳密な段条件を、同じ射の構造正方形へ戻す。 -/
lemma uncurry'_step {U V U' V' : PointedSimplicialSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U ⟶ U') (t : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V ⟶ V')
    (a : 𝟙_ PointedSimplicialSet.{u} ⟶ (ihom U).obj V)
    (b : 𝟙_ PointedSimplicialSet.{u} ⟶ (ihom U').obj V')
    (h : b ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s V' =
      a ≫ suspensionHom U V ≫ PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U) t) :
    PointedSimplicialSet.circle.{u} ◁ uncurry' a ≫ t = s ≫ uncurry' b := by
  apply curry'_injective
  have ha : curry' (PointedSimplicialSet.circle.{u} ◁ uncurry' a ≫ t) =
      a ≫ suspensionHom U V ≫ PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U) t := by
    rw [← curry'_ihom_map, ← suspensionHom_curry', curry'_uncurry']
    rw [Category.assoc]
    rfl
  have hb : curry' (s ≫ uncurry' b) = b ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s V' := by
    rw [← PointedMapping.curry'_pre, curry'_uncurry']
  exact ha.trans (h.symm.trans hb.symm)

/-- 元の全 Hom の単位パラメータの各段を、厳密な列の射として読む。 -/
def homOfPoint (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (a : 𝟙_ PointedSimplicialSet.{u} ⟶ pointedSpace X Y) :
    KanSequence.Hom X.toKanSequence Y where
  app n := uncurry' (a ≫ pointedEvaluation X Y n)
  comm n := by
    apply uncurry'_step (X.sigma n) (Y.sigma n)
    have h := congrArg (a ≫ ·) (pointedEvaluation_condition X Y n)
    simp only [Category.assoc] at h ⊢
    exact h

/-- 元の単位パラメータを列射へ戻して再び点へ移すと、元の全 Hom 内で厳密に戻る。 -/
lemma homPoint_homOfPoint (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (a : 𝟙_ PointedSimplicialSet.{u} ⟶ pointedSpace X Y) :
    homPoint X Y (homOfPoint X Y a) = a := by
  apply pointed_hom_ext X Y
  intro n
  rw [homPoint_evaluation]
  exact curry'_uncurry' _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
