module

public import SerrePositivity.Spectra.SymmetricSequence.ConvolutionMiddleExchange

/-! # 作用と評価の等式をconvolutionの各次数へ降ろす -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

/-- convolutionからの射を二つの次数の標準射上で評価する。 -/
def convolutionComponent {A B D : SymmetricSequence C} (f : A ⊗ B ⟶ D)
    (a b : FiniteBijection) : A.obj a ⊗ B.obj b ⟶ D.obj (a ⊗ b) :=
  (convolutionUnit A B).app (a, b) ≫ f.app (a ⊗ b)

/-- 作用と評価の両立は、各次数では値域の作用とブロック交換によって記述できる。 -/
lemma convolutionComponent_action_evaluation (A M H E : SymmetricSequence C)
    (κ : M ⊗ H ⟶ H) (ev : A ⊗ H ⟶ E) (φ : M ⊗ E ⟶ E)
    (he : A ◁ κ ≫ ev = middleExchange A M H ≫ M ◁ ev ≫ φ)
    (a m h : FiniteBijection) :
    A.obj a ◁ convolutionComponent κ m h ≫ convolutionComponent ev a (m ⊗ h) =
      (α_ (A.obj a) (M.obj m) (H.obj h)).inv ≫
        (β_ (A.obj a) (M.obj m)).hom ▷ H.obj h ≫
          (α_ (M.obj m) (A.obj a) (H.obj h)).hom ≫
            M.obj m ◁ convolutionComponent ev a h ≫ convolutionComponent φ m (a ⊗ h) ≫
              E.map (middleExchangeIndex a m h) := by
  have hx := congrArg (fun k => tripleRightGenerator A M H a m h ≫ k.app (a ⊗ (m ⊗ h))) he
  erw [NatTrans.comp_app, NatTrans.comp_app] at hx
  erw [tripleRightGenerator_middleExchange_assoc] at hx
  erw [(M ◁ ev ≫ φ).naturality] at hx
  unfold tripleRightGenerator at hx
  simp only [Category.assoc] at hx
  erw [NatTrans.comp_app] at hx
  simp only [Category.assoc] at hx
  erw [convolutionUnit_whiskerLeft_assoc, convolutionUnit_whiskerLeft_assoc] at hx
  simp only [← whiskerLeft_comp_assoc] at hx
  unfold convolutionComponent
  simp only [Category.assoc]
  exact hx

end SerrePositivity.SymmetricSequence
