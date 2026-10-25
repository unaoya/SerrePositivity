module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorDegreeExt
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleElements
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso
/-!
概要：相対 tensor の右単位と結合同型の整合式を証明する。
方針：同じ三重斉次生成元で、結合後の Yoneda 評価と先に行う Yoneda 評価を比較する。
規約：元の実 tensor・結合・単位射を保持し、導来圏へ移さない。
使われ方：D-19 の代表加群上の実延長合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C]
  [DGCategory A E] [Small.{u} E] (P : Bimodule A B C) (Q : Bimodule A C E)

lemma rightUnit_associator_value (b : B) (e : E) :
    (associatorValueIso A B C E E P Q (Bimodule.diagonal A E) b e).hom ≫
      composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (rightBimoduleUnitIso A C E Q).hom b e =
    (rightUnitValueIso A B E (compose A B C E P Q) b e).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply associatorLeft_degree_element_ext A B C E E P Q (Bimodule.diagonal A E) b e
  intro c e' k r s i hi hn t q v
  change (composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (rightBimoduleUnitIso A C E Q).hom b e).f n
      ((associatorValueIso A B C E E P Q (Bimodule.diagonal A E) b e).hom.f n
        (associatorLeftElement A B C E E P Q (Bimodule.diagonal A E) b c e' e t q v hi hn)) = _
  rw [associatorValueIso_hom_element A B C E E P Q (Bimodule.diagonal A E)
    b c e' e t q v hi (show k + r = k + r from rfl) hn]
  change (composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (rightBimoduleUnitIso A C E Q).hom b e).f n
      (BalancedTensor.element A C _ _ c
        (BalancedTensor.element A E (representable A e) (Q.leftAt c) e' t q rfl) v (by omega)) =
    (BalancedTensor.yonedaEvaluation A E e ((compose A B C E P Q).leftAt b)).f n
      (BalancedTensor.element A E (representable A e) ((compose A B C E P Q).leftAt b) e' t
        (BalancedTensor.element A C (Q.rightAt e') (P.leftAt b) c q v hi) hn)
  erw [composeValueMap_element A B C E (𝟙 (BimoduleCategory.of A B C P))
    (rightBimoduleUnitIso A C E Q).hom b c e
    (BalancedTensor.element A E (representable A e) (Q.leftAt c) e' t q rfl) v (by omega),
    rightBimoduleUnitIso_hom_value]
  simp only [CategoryTheory.Functor.map_id]
  rw [BalancedTensor.yonedaEvaluation_element]
  change BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c (n := n)
    ((BalancedTensor.yonedaEvaluation A E e (Q.leftAt c)).f (k + r)
      (BalancedTensor.element A E (representable A e) (Q.leftAt c) e' t q rfl)) v (by omega) =
    leftAction A ((compose A B C E P Q).leftAt b) (n := n) t
      (BalancedTensor.element A C (Q.rightAt e') (P.leftAt b) c q v hi) (by omega)
  rw [BalancedTensor.yonedaEvaluation_element]
  exact (compose_leftAction_element A B C E P Q b c e' e
    (p := k) (k := r) (r := s) (i := i) (j := k + r) (n := n)
    hi (by omega) (by omega) t q v).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
