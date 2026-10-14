module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomTransport
public import SerrePositivity.Spectra.SymmetricSequence.Limits
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomSequenceIso
public import SerrePositivity.Spectra.SymmetricSequence.ConvolutionActionEvaluation

/-! # 次数をずらした内部Homの生成元上の評価 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 対称列の比較を介して次数をずらした内部Homから評価する。 -/
def freeShiftEvaluation (n : ℕ) (X : C) (F : SymmetricSequence C) :
    (freeAt n).obj X ⊗ shiftedInternalHom n X F ⟶ F :=
  (freeAt n).obj X ◁ (freeInternalHomSequenceIso n X F).inv ≫
    (ihom.ev ((freeAt n).obj X)).app F

/-- 第n段の生成元に制限した評価は、和次数への通常の内部Homの評価。 -/
@[reassoc]
lemma freeShiftEvaluation_generator (n q : ℕ) (X : C) (F : SymmetricSequence C) :
    freeAtGenerator n X ▷ level (shiftedInternalHom n X F) q ≫
      convolutionComponent (freeShiftEvaluation n X F) (FiniteBijection.of n)
        (FiniteBijection.of q) = (ihom.ev X).app (level F (n + q)) := by
  unfold convolutionComponent freeShiftEvaluation
  erw [NatTrans.comp_app, convolutionUnit_whiskerLeft_assoc]
  erw [← whisker_exchange_assoc]
  erw [convolutionUnit_evaluation]
  rw [← uncurry_pre_app]
  erw [← freeInternalHomLevelIso_hom_projection]
  rw [freeInternalHomSequenceIso_inv_app, uncurry_eq]
  rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  rfl

variable [HasEqualizers (SymmetricSequence C)]

variable (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]

/-- 次数をずらした内部Homへ係数作用を移した加群。 -/
def freeShiftModule (n : ℕ) (X : C) (F : Mod (SymmetricSequence C) M) :
    Mod (SymmetricSequence C) M :=
  MonoidalModuleInternalHom.transportedObj M ((freeAt n).obj X) F
    (freeInternalHomSequenceIso n X F.X)

/-- 生成元に制限した各次数の作用は値域の作用と添字の交換で記述できる。 -/
@[reassoc]
lemma freeShiftModule_action_component_evaluation (n p q : ℕ) (X : C)
    (F : Mod (SymmetricSequence C) M) :
    X ◁ convolutionComponent γ[M, (freeShiftModule M n X F).X]
        (FiniteBijection.of p) (FiniteBijection.of q) ≫
      (ihom.ev X).app (level F.X (n + (p + q))) =
    (α_ X (level M p) (level (shiftedInternalHom n X F.X) q)).inv ≫
      (β_ X (level M p)).hom ▷ level (shiftedInternalHom n X F.X) q ≫
        (α_ (level M p) X (level (shiftedInternalHom n X F.X) q)).hom ≫
          level M p ◁ (ihom.ev X).app (level F.X (n + q)) ≫
            convolutionComponent γ[M, F.X] (FiniteBijection.of p)
              (FiniteBijection.of (n + q)) ≫
                F.X.map (middleExchangeIndex (FiniteBijection.of n)
                  (FiniteBijection.of p) (FiniteBijection.of q)) := by
  have he0 := MonoidalModuleInternalHom.transportedObj_action_evaluation M
    ((freeAt n).obj X) F (freeInternalHomSequenceIso n X F.X)
  have he : (freeAt n).obj X ◁ γ[M, (freeShiftModule M n X F).X] ≫
      freeShiftEvaluation n X F.X =
    middleExchange ((freeAt n).obj X) M (freeShiftModule M n X F).X ≫
      M ◁ freeShiftEvaluation n X F.X ≫ γ[M, F.X] := by
    unfold middleExchange
    simp only [Category.assoc]
    exact he0
  have h := convolutionComponent_action_evaluation ((freeAt n).obj X) M
    (freeShiftModule M n X F).X F.X γ[M, (freeShiftModule M n X F).X]
    (freeShiftEvaluation n X F.X) γ[M, F.X] he
    (FiniteBijection.of n) (FiniteBijection.of p) (FiniteBijection.of q)
  have hh := congrArg (fun k => freeAtGenerator n X ▷
    (level M p ⊗ level (shiftedInternalHom n X F.X) q) ≫ k) h
  erw [← whisker_exchange_assoc, freeShiftEvaluation_generator] at hh
  erw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left, comp_whiskerRight] at hh
  simp only [Category.assoc] at hh
  erw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    freeShiftEvaluation_generator] at hh
  exact hh

end SerrePositivity.SymmetricSequence
