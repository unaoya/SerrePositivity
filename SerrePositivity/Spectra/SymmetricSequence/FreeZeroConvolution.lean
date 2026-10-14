module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorHom
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 生成次数零の左convolutionと各段の通常のテンソル積 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 自由原変数の内部Homの生成次数零の比較を値域関手の自然同型にまとめる。 -/
def freeZeroInternalHomNatIso (X : C) :
    ihom ((freeAt 0).obj X) ≅ unshiftedInternalHomFunctor X :=
  NatIso.ofComponents (fun F =>
    freeInternalHomSequenceIso 0 X F ≪≫ zeroShiftInternalHomIso X F) (by
      intro F G g
      apply hom_ext
      intro q
      change ((ihom ((freeAt 0).obj X)).map g).app (FiniteBijection.of q) ≫
          (freeInternalHomLevelIso 0 q X G).hom ≫
            (zeroShiftInternalHomIso X G).hom.app (FiniteBijection.of q) =
        ((freeInternalHomLevelIso 0 q X F).hom ≫
          (zeroShiftInternalHomIso X F).hom.app (FiniteBijection.of q)) ≫
            (ihom X).map (g.app (FiniteBijection.of q))
      simp only [Category.assoc]
      rw [freeInternalHomLevelIso_naturality_assoc]
      change (freeInternalHomLevelIso 0 q X F).hom ≫
          (ihom X).map (g.app ((𝟙_ FiniteBijection) ⊗ FiniteBijection.of q)) ≫
            (ihom X).map (G.map (λ_ (FiniteBijection.of q)).hom) =
        (freeInternalHomLevelIso 0 q X F).hom ≫
          (ihom X).map (F.map (λ_ (FiniteBijection.of q)).hom) ≫
            (ihom X).map (g.app (FiniteBijection.of q))
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        g.naturality]
      rfl)

/-- 生成次数零のconvolutionの右随伴を通常の内部Homへ比較した随伴。 -/
def freeZeroConvolutionAdjunction (X : C) :
    tensorLeft ((freeAt 0).obj X) ⊣ unshiftedInternalHomFunctor X :=
  (ihom.adjunction ((freeAt 0).obj X)).ofNatIsoRight (freeZeroInternalHomNatIso X)

/-- 左随伴の一意性による生成次数零のconvolutionの各段の比較。 -/
def freeZeroConvolutionNatIso (X : C) :
    tensorLeft ((freeAt 0).obj X) ≅ pointwiseTensorFunctor X :=
  (freeZeroConvolutionAdjunction X).leftAdjointUniq (pointwiseTensorHomAdjunction X)

/-- 生成次数零の左convolutionの第q段はXとの通常のテンソル積。 -/
def freeZeroConvolutionLevelIso (X : C) (F : SymmetricSequence C) (q : ℕ) :
    level (((freeAt 0).obj X) ⊗ F) q ≅ X ⊗ level F q :=
  (evaluation q).mapIso ((freeZeroConvolutionNatIso X).app F)

/-- 左随伴の比較は評価と両立する。 -/
@[reassoc]
lemma freeZeroConvolutionNatIso_evaluation (X : C) (F : SymmetricSequence C) :
    (freeZeroConvolutionNatIso X).hom.app (unshiftedInternalHom X F) ≫
        (pointwiseTensorHomAdjunction X).counit.app F =
      (freeZeroConvolutionAdjunction X).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit
    (freeZeroConvolutionAdjunction X) (pointwiseTensorHomAdjunction X) F

/-- 各段の比較は通常の内部Homの評価を、自由対称列からの評価へ戻す。 -/
lemma freeZeroConvolutionLevelIso_evaluation (X : C) (F : SymmetricSequence C) (q : ℕ) :
    (freeZeroConvolutionLevelIso X (unshiftedInternalHom X F) q).hom ≫
        (ihom.ev X).app (level F q) =
      (((freeAt 0).obj X ◁ (freeZeroInternalHomNatIso X).inv.app F) ≫
        (ihom.ev ((freeAt 0).obj X)).app F).app (FiniteBijection.of q) := by
  have h := congrArg (fun k => k.app (FiniteBijection.of q))
    (freeZeroConvolutionNatIso_evaluation X F)
  change (freeZeroConvolutionLevelIso X (unshiftedInternalHom X F) q).hom ≫
      ((pointwiseTensorHomAdjunction X).counit.app F).app (FiniteBijection.of q) = _ at h
  rw [pointwiseTensorHomAdjunction_counit_app] at h
  exact h

/-- 通常のテンソル積から逆比較を介した評価は通常の内部Homの評価。 -/
lemma freeZeroConvolutionLevelIso_inv_evaluation (X : C) (F : SymmetricSequence C) (q : ℕ) :
    (freeZeroConvolutionLevelIso X (unshiftedInternalHom X F) q).inv ≫
        (((freeAt 0).obj X ◁ (freeZeroInternalHomNatIso X).inv.app F) ≫
          (ihom.ev ((freeAt 0).obj X)).app F).app (FiniteBijection.of q) =
      (ihom.ev X).app (level F q) := by
  rw [← freeZeroConvolutionLevelIso_evaluation]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.SymmetricSequence
