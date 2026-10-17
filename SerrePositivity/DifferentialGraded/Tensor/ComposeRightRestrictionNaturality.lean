module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestriction
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 外側右制限の合成比較と両因子の閉零射の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)

/-- 外側右制限と合成の比較は、両因子の任意の全Hom自然な閉零射に自然。 -/
lemma composeRightRestrictionIso_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    composeMap A D C E ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map f) g ≫
        (composeRightRestrictionIso A B D C E F P' Q').hom =
      (composeRightRestrictionIso A B D C E F P Q).hom ≫
        (BimoduleCategory.middleRightRestrictionFunctor A B D E F).map
          (composeMap A B C E f g) := by
  apply BimoduleCategory.value_hom_ext A D E
  intro d e
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    composeRightRestrictionIso_hom_value]
  refine Eq.trans ?_ (congrArg (fun k =>
    (composeRightRestrictionValueIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e).hom ≫ k)
    (BimoduleCategory.middleRightRestrictionMap_value_eval A B D E F
      (composeMap A B C E f g) d e)).symm
  rw [composeMap_value_eval]
  apply BalancedTensor.hom_ext A C ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P)).leftAt d)
  intro c
  have h₁ := ι_composeValueMap A D C E
    ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map f) g d c e
  have h₂ := ι_composeRightRestrictionValueIso_hom A B D C E F
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') d e c
  have h₃ := ι_composeRightRestrictionValueIso_hom A B D C E F
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e c
  have h₄ := ι_composeValueMap A B C E f g (F.obj d) c e
  have hl := (congrArg (fun k => k ≫
      (composeRightRestrictionValueIso A B D C E F
        (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q') d e).hom) h₁).trans (by
    simpa only [Category.assoc, BimoduleCategory.middleRightRestrictionFunctor,
      BimoduleCategory.underlying, BimoduleCategory.of] using congrArg (fun k =>
      ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ
        (BimoduleCategory.valueEvaluation A D C d c).map
          ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map f)) ≫ k) h₂)
  have hr := (congrArg (fun k => k ≫ composeValueMap A B C E f g (F.obj d) e) h₃).trans h₄
  have hm := congrArg (fun k => ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ k) ≫
    BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt (F.obj d)) c)
    (BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F f d c)
  simpa only [Category.assoc, BimoduleCategory.middleRightRestrictionFunctor,
      BimoduleCategory.underlying, BimoduleCategory.of] using hl.trans (hm.trans hr.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
