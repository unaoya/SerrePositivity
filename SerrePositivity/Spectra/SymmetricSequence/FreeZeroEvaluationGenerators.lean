module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolution
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomShiftEvaluation

/-! # 生成次数零の内部Homの通常の各段の生成元上の評価 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 生成次数零の通常の内部Homの対称列からの評価。 -/
def freeZeroEvaluation (X : C) (F : SymmetricSequence C) :
    (freeAt 0).obj X ⊗ unshiftedInternalHom X F ⟶ F :=
  (freeAt 0).obj X ◁ (zeroShiftInternalHomIso X F).inv ≫ freeShiftEvaluation 0 X F

/-- この評価は自由原変数の内部Homの逆比較を介した評価。 -/
lemma freeZeroEvaluation_eq (X : C) (F : SymmetricSequence C) :
    freeZeroEvaluation X F = (freeAt 0).obj X ◁ (freeZeroInternalHomNatIso X).inv.app F ≫
      (ihom.ev ((freeAt 0).obj X)).app F := by
  unfold freeZeroEvaluation freeShiftEvaluation
  rw [← whiskerLeft_comp_assoc]
  rfl

/-- 生成元に制限し零次の添字移送を除くと、通常の内部Homの評価になる。 -/
@[reassoc]
lemma freeZeroEvaluation_generator (X : C) (F : SymmetricSequence C) (q : ℕ) :
    freeAtGenerator 0 X ▷ level (unshiftedInternalHom X F) q ≫
      convolutionComponent (freeZeroEvaluation X F) (FiniteBijection.of 0)
        (FiniteBijection.of q) ≫ F.map (λ_ (FiniteBijection.of q)).hom =
      (ihom.ev X).app (level F q) := by
  unfold convolutionComponent freeZeroEvaluation
  erw [NatTrans.comp_app, convolutionUnit_whiskerLeft_assoc]
  simp only [Category.assoc]
  erw [← whisker_exchange_assoc]
  erw [← Category.assoc
    ((convolutionUnit ((freeAt 0).obj X) (shiftedInternalHom 0 X F)).app
      (FiniteBijection.of 0, FiniteBijection.of q))
    ((freeShiftEvaluation 0 X F).app (FiniteBijection.of 0 ⊗ FiniteBijection.of q))
    (F.map (λ_ (FiniteBijection.of q)).hom)]
  change X ◁ (zeroShiftInternalHomIso X F).inv.app (FiniteBijection.of q) ≫
    freeAtGenerator 0 X ▷ level (shiftedInternalHom 0 X F) q ≫
      convolutionComponent (freeShiftEvaluation 0 X F) (FiniteBijection.of 0)
        (FiniteBijection.of q) ≫ F.map (λ_ (FiniteBijection.of q)).hom = _
  erw [freeShiftEvaluation_generator_assoc]
  change X ◁ (ihom X).map (F.map (λ_ (FiniteBijection.of q)).inv) ≫
    (ihom.ev X).app (level F (0 + q)) ≫ F.map (λ_ (FiniteBijection.of q)).hom = _
  erw [(ihom.ev X).naturality_assoc]
  simp only [CategoryTheory.Functor.id_map]
  erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

/-- 第0段の生成元と第q段の対象からconvolutionの第q段へ入る標準射。 -/
def freeZeroConvolutionGenerator (X : C) (F : SymmetricSequence C) (q : ℕ) :
    X ⊗ level F q ⟶ level ((freeAt 0).obj X ⊗ F) q :=
  freeAtGenerator 0 X ▷ level F q ≫
    (convolutionUnit ((freeAt 0).obj X) F).app (FiniteBijection.of 0, FiniteBijection.of q) ≫
      (((freeAt 0).obj X) ⊗ F).map (λ_ (FiniteBijection.of q)).hom

/-- 自由零生成対称列の逆転置は通常の内部Homへの射をテンソルして評価する合成。 -/
lemma freeZeroConvolutionUncurry_eq (X : C) {F G : SymmetricSequence C}
    (h : F ⟶ unshiftedInternalHom X G) :
    ((freeZeroConvolutionAdjunction X).homEquiv F G).symm h =
      (freeAt 0).obj X ◁ h ≫ freeZeroEvaluation X G := by
  unfold freeZeroConvolutionAdjunction
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  change uncurry (h ≫ (freeZeroInternalHomNatIso X).inv.app G) = _
  rw [uncurry_eq, whiskerLeft_comp, Category.assoc, freeZeroEvaluation_eq]

/-- 自由零生成対称列の逆転置は生成元上で通常の各段の逆転置になる。 -/
lemma freeZeroConvolutionUncurry_generator (X : C) {F G : SymmetricSequence C}
    (h : F ⟶ unshiftedInternalHom X G) (q : ℕ) :
    freeZeroConvolutionGenerator X F q ≫
        (((freeZeroConvolutionAdjunction X).homEquiv F G).symm h).app
          (FiniteBijection.of q) = uncurry (h.app (FiniteBijection.of q)) := by
  rw [freeZeroConvolutionUncurry_eq]
  unfold freeZeroConvolutionGenerator
  simp only [Category.assoc]
  erw [NatTrans.naturality]
  erw [NatTrans.comp_app]
  simp only [Category.assoc]
  erw [convolutionUnit_whiskerLeft_assoc]
  erw [← whisker_exchange_assoc]
  erw [← Category.assoc
    ((convolutionUnit ((freeAt 0).obj X) (unshiftedInternalHom X G)).app
      (FiniteBijection.of 0, FiniteBijection.of q))
    ((freeZeroEvaluation X G).app (FiniteBijection.of 0 ⊗ FiniteBijection.of q))
    (G.map (λ_ (FiniteBijection.of q)).hom)]
  change X ◁ h.app (FiniteBijection.of q) ≫
    (freeAtGenerator 0 X ▷ level (unshiftedInternalHom X G) q ≫
      convolutionComponent (freeZeroEvaluation X G) (FiniteBijection.of 0)
        (FiniteBijection.of q) ≫ G.map (λ_ (FiniteBijection.of q)).hom) = _
  erw [freeZeroEvaluation_generator, uncurry_eq]
  rfl

omit [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] in
/-- 点ごとの随伴の単位の各段は通常の内部Homの余評価。 -/
lemma pointwiseTensorHomAdjunction_unit_app (X : C) (F : SymmetricSequence C)
    (a : FiniteBijection) :
    ((pointwiseTensorHomAdjunction X).unit.app F).app a = (ihom.coev X).app (F.obj a) :=
  Adjunction.whiskerRight_unit_app_app FiniteBijection (ihom.adjunction X) F a

/-- 生成次数零のconvolutionの比較は生成元からの標準射を恒等射へ送る。 -/
@[reassoc]
lemma freeZeroConvolutionGenerator_comparison (X : C) (F : SymmetricSequence C) (q : ℕ) :
    freeZeroConvolutionGenerator X F q ≫
        (freeZeroConvolutionLevelIso X F q).hom = 𝟙 (X ⊗ level F q) := by
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (freeZeroConvolutionAdjunction X) (pointwiseTensorHomAdjunction X) F
  change (freeZeroConvolutionAdjunction X).homEquiv F ((pointwiseTensorFunctor X).obj F)
    ((freeZeroConvolutionNatIso X).hom.app F) = (pointwiseTensorHomAdjunction X).unit.app F at hu
  have h := freeZeroConvolutionUncurry_generator X
    ((freeZeroConvolutionAdjunction X).homEquiv F ((pointwiseTensorFunctor X).obj F)
      ((freeZeroConvolutionNatIso X).hom.app F)) q
  rw [Equiv.symm_apply_apply] at h
  change freeZeroConvolutionGenerator X F q ≫ (freeZeroConvolutionLevelIso X F q).hom = _ at h
  rw [hu, pointwiseTensorHomAdjunction_unit_app] at h
  erw [← curry_id_eq_coev, uncurry_curry] at h
  exact h

/-- 各段の逆比較は第0段の生成元からの標準射に一致する。 -/
lemma freeZeroConvolutionGenerator_eq_inv (X : C) (F : SymmetricSequence C) (q : ℕ) :
    freeZeroConvolutionGenerator X F q = (freeZeroConvolutionLevelIso X F q).inv := by
  apply (cancel_mono (freeZeroConvolutionLevelIso X F q).hom).mp
  rw [freeZeroConvolutionGenerator_comparison]
  exact (freeZeroConvolutionLevelIso X F q).inv_hom_id.symm

end SerrePositivity.SymmetricSequence
