module
public import SerrePositivity.KST.SConstruction.DGTensorLeftUnitElements
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorDegreeExt
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 元の tensor 左単位と結合同型の両立
概要：左端の単位を消す経路と、結合後に単位を消す経路の一致を示す。
方針：元の単位同型の逆で前合成し、次数零の単位挿入で全次数の生成元を比較する。
規約：元の結合・単位射を保つ。使われ方：右恒等 dg 入力の実 Perf 単位法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C] [DGCategory A E]
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 右括弧の三重生成元への単位挿入は、合成双加群への同じ挿入である。 -/
lemma dgTensorLeftUnit_associatorRight_insert (b : B) (c : C) (e : E)
    {k r n : ℤ} (hn : k + r = n) (t : (Q.value c e).X k) (q : (P.value b c).X r) :
    BimoduleTensor.associatorRightElement A B B C E (Bimodule.diagonal A B) P Q
        b b c e t q (unitElement A b).val hn (add_zero n) =
      BalancedTensor.element A B ((BimoduleTensor.compose A B C E P Q).rightAt e)
        ((Bimodule.diagonal A B).leftAt b) b
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c t q hn)
        (unitElement A b).val (add_zero n) := rfl

/-- 逆単位で前合成した結合・単位の経路は、元の全次数生成元を回収する。 -/
lemma dgTensorLeftUnit_associator_inverse_element (b : B) (c : C) (e : E)
    {k r n : ℤ} (hn : k + r = n) (t : (Q.value c e).X k) (q : (P.value b c).X r) :
    (BimoduleTensor.leftUnitValueIso A B E (BimoduleTensor.compose A B C E P Q) b e).hom.f n
      ((BimoduleTensor.associatorValueIso A B B C E (Bimodule.diagonal A B) P Q b e).hom.f n
        ((BimoduleTensor.composeValueMap A B C E
          (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
          (𝟙 (BimoduleCategory.of A C E Q)) b e).f n
          (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c t q hn))) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c t q hn := by
  have hm := dgTensorLeftUnit_inverse_map_element A B C E P Q b c e hn t q
  have ha := BimoduleTensor.associatorValueIso_hom_element A B B C E
    (Bimodule.diagonal A B) P Q b b c e t q (unitElement A b).val (add_zero r) hn hn
  have ht := (dgComplexMap_apply_congr
    (BimoduleTensor.associatorValueIso A B B C E (Bimodule.diagonal A B) P Q b e).hom n
    hm).trans ha
  have hi := ht.trans (dgTensorLeftUnit_associatorRight_insert A B C E P Q b c e hn t q)
  have he := dgComplexMap_apply_congr (BimoduleTensor.leftUnitValueIso A B E
    (BimoduleTensor.compose A B C E P Q) b e).hom n hi
  have hu := dgBimoduleLeftUnit_hom_insert A B E
    (BimoduleTensor.compose A B C E P Q) b e n
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c t q hn)
  exact he.trans hu

end SerrePositivity.KST.SConstruction
