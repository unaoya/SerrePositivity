module
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap
public import SerrePositivity.DifferentialGraded.Tensor.ComposeLeftRestriction
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso

/-! # 対角のHom比較と中間制限比較による右単位子の保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

/-- 対角比較をtensorし、中間比較とYoneda評価を続けると制限後の右単位になる。 -/
lemma rightUnitRestriction_value (P : BimoduleCategory A B C) (b : B) (d : D) :
    composeValueMap A B D D
        (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P))
        (Bimodule.diagonalRestrictionMap A D C F) b d ≫
      middleRestrictionComparisonValue A B C D D F (BimoduleCategory.underlying A B C P)
        (Bimodule.leftRestriction A C C D F (Bimodule.diagonal A C)) b d ≫
      (rightUnitValueIso A B C (BimoduleCategory.underlying A B C P) b (F.obj d)).hom =
    (rightUnitValueIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)) b d).hom := by
  apply BalancedTensor.hom_ext
  intro x
  erw [ι_composeValueMap_assoc A B D D
    (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P))
    (Bimodule.diagonalRestrictionMap A D C F) b x d, Bimodule.diagonalRestrictionMap_value,
    CategoryTheory.Functor.map_id]
  erw [ι_middleRestrictionComparisonValue_assoc A B C D D F
    (BimoduleCategory.underlying A B C P)
    (Bimodule.leftRestriction A C C D F (Bimodule.diagonal A C)) b d x]
  change (F.map x d ⊗ₘ 𝟙 _) ≫ BalancedTensor.ι A C
      (representable A (F.obj d)) ((BimoduleCategory.underlying A B C P).leftAt b)
      (F.obj x) ≫ BalancedTensor.yonedaEvaluation A C (F.obj d)
        ((BimoduleCategory.underlying A B C P).leftAt b) =
    BalancedTensor.ι A D (representable A d)
      ((Bimodule.leftRestriction A B C D F
        (BimoduleCategory.underlying A B C P)).leftAt b) x ≫
      BalancedTensor.yonedaEvaluation A D d
        ((Bimodule.leftRestriction A B C D F
          (BimoduleCategory.underlying A B C P)).leftAt b)
  rw [BalancedTensor.ι_yonedaEvaluation, BalancedTensor.ι_yonedaEvaluation]
  have hl : BalancedTensor.leftAction A D
      ((Bimodule.leftRestriction A B C D F
        (BimoduleCategory.underlying A B C P)).leftAt b) x d =
    BalancedTensor.leftAction A D (F.comp ((BimoduleCategory.underlying A B C P).leftAt b))
      x d := by
    change uncurryRight ((F.map x d ≫ (BimoduleCategory.underlying A B C P).map
      (F.obj x) (F.obj d)) ≫ moduleHomπ A B _ _ b) =
      uncurryRight (F.map x d ≫ ((BimoduleCategory.underlying A B C P).map
        (F.obj x) (F.obj d) ≫ moduleHomπ A B _ _ b))
    rw [Category.assoc]
  rw [hl]
  exact (BalancedTensor.leftAction_restrict A D C F
    ((BimoduleCategory.underlying A B C P).leftAt b) x d).symm

/-- 右単位子は対角のHom比較・中間比較・外側左制限比較と整合する。 -/
lemma rightUnitRestriction (P : BimoduleCategory A B C) :
    composeMap A B D D
        (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P))
        (Bimodule.diagonalRestrictionMap A D C F) ≫
      middleRestrictionComparisonMap A B C D D F (BimoduleCategory.underlying A B C P)
        (Bimodule.leftRestriction A C C D F (Bimodule.diagonal A C)) ≫
      (composeLeftRestrictionIso A B C C D F P
        (BimoduleCategory.of A C C (Bimodule.diagonal A C))).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (rightBimoduleUnitIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))).hom := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    middleRestrictionComparisonMap_value_eval, composeLeftRestrictionIso_hom_value]
  erw [BimoduleCategory.middleLeftRestrictionMap_value_eval]
  rw [rightBimoduleUnitIso_hom_value, rightBimoduleUnitIso_hom_value]
  erw [Category.id_comp]
  exact rightUnitRestriction_value A B C D F P b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
