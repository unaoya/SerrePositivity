module
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorGenerators
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Complexes.TensorGeneratorMaps

/-! # 単位と結合比較の三角図式を三重包含上で計算する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma triangleLeft_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (x y : C) (e : E) :
    associatorLeftι A B C C E P (Bimodule.diagonal A C) Q b x y e ≫
      composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
        (𝟙 (BimoduleCategory.of A C E Q)) b e =
    Q.value y e ◁ BalancedTensor.leftAction A C (P.leftAt b) x y ≫
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) y := by
  have ho := ι_composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
    (𝟙 (BimoduleCategory.of A C E Q)) b y e
  rw [CategoryTheory.Functor.map_id, rightBimoduleUnitIso_hom_value] at ho
  exact tensorLeft_generator_map
    (BalancedTensor.ι A C ((Bimodule.diagonal A C).rightAt y) (P.leftAt b) x)
    (BalancedTensor.ι A C (Q.rightAt e) ((compose A B C C P (Bimodule.diagonal A C)).leftAt b) y)
    (composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) b e)
    (rightUnitValueIso A B C P b y).hom
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) y)
    (BalancedTensor.leftAction A C (P.leftAt b) x y) ho
    (BalancedTensor.ι_yonedaEvaluation A C y (P.leftAt b) x)

lemma triangleRight_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (x y : C) (e : E) :
    associatorLeftι A B C C E P (Bimodule.diagonal A C) Q b x y e ≫
      ((associatorValueIso A B C C E P (Bimodule.diagonal A C) Q b e).hom ≫
        composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
          (leftBimoduleUnitIso A C E Q).hom b e) =
    (α_ (Q.value y e) (x ⟶[Complex A] y) (P.value b x)).inv ≫
      (BalancedTensor.rightAction A C (Q.rightAt e) x y ▷ P.value b x) ≫
        BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) x := by
  have ho := ι_composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
    (leftBimoduleUnitIso A C E Q).hom b x e
  rw [CategoryTheory.Functor.map_id, leftBimoduleUnitIso_hom_value] at ho
  have hc := congrArg (fun k => k ≫ composeValueMap A B C E
    (𝟙 (BimoduleCategory.of A B C P)) (leftBimoduleUnitIso A C E Q).hom b e)
    (associatorLeftι_hom A B C C E P (Bimodule.diagonal A C) Q b x y e)
  have ht := tensorRight_generator_map
    (BalancedTensor.ι A C (Q.rightAt e) ((Bimodule.diagonal A C).leftAt x) y)
    (BalancedTensor.ι A C ((compose A C C E (Bimodule.diagonal A C) Q).rightAt e)
      (P.leftAt b) x)
    (composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (leftBimoduleUnitIso A C E Q).hom b e)
    (leftUnitValueIso A C E Q x e).hom
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) x)
    (BalancedTensor.rightAction A C (Q.rightAt e) x y) ho
    (ι_leftUnitValueIso_hom A C E Q x y e)
  exact (Category.assoc _ _ _).symm.trans (hc.trans ht)

end SerrePositivity.DifferentialGraded.BimoduleTensor
