module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 中間dg圏の合成比較射の両因子に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

lemma middleRestrictionComparisonValue_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    composeValueMap A B D E (BimoduleCategory.middleLeftRestrictionMap A B C D F f)
        (BimoduleCategory.middleRightRestrictionMap A C D E F g) b e ≫
      middleRestrictionComparisonValue A B C D E F
        (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') b e =
    middleRestrictionComparisonValue A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) b e ≫
      composeValueMap A B C E f g b e := by
  apply BalancedTensor.hom_ext
  intro d
  have hs := ι_composeValueMap A B D E
    (BimoduleCategory.middleLeftRestrictionMap A B C D F f)
    (BimoduleCategory.middleRightRestrictionMap A C D E F g) b d e
  simp only [BimoduleCategory.middleLeftRestrictionMap_value_eval,
    BimoduleCategory.middleRightRestrictionMap_value_eval] at hs
  have ht := ι_composeValueMap A B C E f g b (F.obj d) e
  have hc := ι_middleRestrictionComparisonValue A B C D E F
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') b e d
  have hp := ι_middleRestrictionComparisonValue_assoc A B C D E F
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) b e d
      (composeValueMap A B C E f g b e)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ middleRestrictionComparisonValue A B C D E F
      (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') b e) hs).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => ((BimoduleCategory.valueEvaluation A C E (F.obj d) e).map g ⊗ₘ
          (BimoduleCategory.valueEvaluation A B C b (F.obj d)).map f) ≫ k) hc).trans
            (ht.symm.trans hp.symm))))

/-- 既存の合成双関手の射と実際の中間圏比較射が両変数で可換。 -/
lemma middleRestrictionComparisonMap_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    composeMap A B D E (BimoduleCategory.middleLeftRestrictionMap A B C D F f)
        (BimoduleCategory.middleRightRestrictionMap A C D E F g) ≫
      middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') =
    middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) ≫
      composeMap A B C E f g := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    middleRestrictionComparisonMap_value_eval]
  exact middleRestrictionComparisonValue_naturality A B C D E F f g b e

/-- 制限してから合成する、既存の関手の積と合成からなる関手。 -/
def middleRestrictedComposeFunctor :
    BimoduleCategory A B C × BimoduleCategory A C E ⥤ BimoduleCategory A B E :=
  ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).prod
    (BimoduleCategory.middleRightRestrictionFunctor A C D E F)) ⋙ composeFunctor A B D E

/-- 実際の閉零bimodule圏の積上の中間圏比較自然変換。 -/
def middleRestrictionComparisonNatTrans :
    middleRestrictedComposeFunctor A B C D E F ⟶ composeFunctor A B C E where
  app PQ := middleRestrictionComparisonMap A B C D E F
    (BimoduleCategory.underlying A B C PQ.1) (BimoduleCategory.underlying A C E PQ.2)
  naturality {_X _Y} f := middleRestrictionComparisonMap_naturality A B C D E F f.1 f.2

end SerrePositivity.DifferentialGraded.BimoduleTensor
