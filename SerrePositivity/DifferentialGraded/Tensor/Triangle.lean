module
public import SerrePositivity.DifferentialGraded.Tensor.TriangleGenerators
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation

/-! # 閉零bimodule圏の単位・結合比較の三角coherence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma triangleValue (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) :
    composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) b e =
    (associatorValueIso A B C C E P (Bimodule.diagonal A C) Q b e).hom ≫
      composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (leftBimoduleUnitIso A C E Q).hom b e := by
  apply associatorLeft_hom_ext A B C C E P (Bimodule.diagonal A C) Q b e
  intro x y
  have hb := tensor_associator_balance
    (BalancedTensor.rightAction A C (Q.rightAt e) x y)
    (BalancedTensor.leftAction A C (P.leftAt b) x y)
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) x)
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) y)
    (BalancedTensor.condition A C (Q.rightAt e) (P.leftAt b) x y)
  exact (triangleLeft_ι A B C E P Q b x y e).trans
    (hb.trans (triangleRight_ι A B C E P Q b x y e).symm)

/-- 対角Cを中間に挿入する三角図式は、実際の閉零bimodule射として可換。 -/
lemma triangle (P : Bimodule A B C) (Q : Bimodule A C E) :
    composeMap A B C E (rightBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) =
    (associatorIso A B C C E P (Bimodule.diagonal A C) Q).hom ≫
      composeMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (leftBimoduleUnitIso A C E Q).hom := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    associatorIso_hom_value_eval]
  exact triangleValue A B C E P Q b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
