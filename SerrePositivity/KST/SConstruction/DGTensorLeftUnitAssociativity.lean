module
public import SerrePositivity.KST.SConstruction.DGTensorLeftUnitInsertion
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions

/-! # 元の tensor 左単位と結合同型の両立
概要：左端の単位を消す経路と、結合後に単位を消す経路の一致を示す。
方針：元の単位同型の逆で前合成し、coend 包含上の挿入と回収の式で比較する。
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

/-- 逆単位で前合成した結合・単位の経路は元の合成複体の恒等射である。 -/
lemma dgTensorLeftUnit_associator_inverse_value (b : B) (e : E) :
    BimoduleTensor.composeValueMap A B C E
        (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
        (𝟙 (BimoduleCategory.of A C E Q)) b e ≫
      (BimoduleTensor.associatorValueIso A B B C E (Bimodule.diagonal A B) P Q b e).hom ≫
        (BimoduleTensor.leftUnitValueIso A B E (BimoduleTensor.compose A B C E P Q) b e).hom =
      𝟙 ((BimoduleTensor.compose A B C E P Q).value b e) := by
  apply BalancedTensor.hom_ext A C (Q.rightAt e) (P.leftAt b)
    (T := (BimoduleTensor.compose A B C E P Q).value b e)
  intro c
  have hu := dgDiagonalUnitInsertion_evaluation A B
    ((BimoduleTensor.compose A B C E P Q).rightAt e) b
  change dgDiagonalUnitInsertion A B ((BimoduleTensor.compose A B C E P Q).rightAt e) b ≫
    (BimoduleTensor.leftUnitValueIso A B E (BimoduleTensor.compose A B C E P Q) b e).hom =
      𝟙 ((BimoduleTensor.compose A B C E P Q).value b e) at hu
  exact dgComplex_triple_generator_of_unit A
    (X := (BimoduleTensor.compose A B C E P Q).value b e)
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c)
    (BimoduleTensor.composeValueMap A B C E
      (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
      (𝟙 (BimoduleCategory.of A C E Q)) b e)
    (BimoduleTensor.associatorValueIso A B B C E (Bimodule.diagonal A B) P Q b e).hom
    (BimoduleTensor.leftUnitValueIso A B E (BimoduleTensor.compose A B C E P Q) b e).hom
    (dgDiagonalUnitInsertion A B ((BimoduleTensor.compose A B C E P Q).rightAt e) b)
    (dgTensorLeftUnit_inverse_associator_iota A B C E P Q b c e) hu

/-- 左単位と結合の両経路は、元の各値の chain map として一致する。 -/
lemma dgTensorLeftUnit_associator_value (b : B) (e : E) :
    (BimoduleTensor.associatorValueIso A B B C E (Bimodule.diagonal A B) P Q b e).hom ≫
        (BimoduleTensor.leftUnitValueIso A B E (BimoduleTensor.compose A B C E P Q) b e).hom =
      BimoduleTensor.composeValueMap A B C E
        (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
        (𝟙 (BimoduleCategory.of A C E Q)) b e := by
  exact dgComplexIso_hom_eq_of_inv_comp (dgTensorLeftUnitMapValueIso A B C E P Q b e) _
    (dgTensorLeftUnit_associator_inverse_value A B C E P Q b e)

/-- 左単位と結合の両経路は、全 Hom 自然な元の双加群射として一致する。 -/
lemma dgTensorLeftUnit_associator :
    (BimoduleTensor.associatorIso A B B C E (Bimodule.diagonal A B) P Q).hom ≫
        (BimoduleTensor.leftBimoduleUnitIso A B E (BimoduleTensor.compose A B C E P Q)).hom =
      BimoduleTensor.composeMap A B C E
        (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
        (𝟙 (BimoduleCategory.of A C E Q)) := by
  apply BimoduleCategory.value_hom_ext
  intro b e
  simp only [Functor.map_comp, BimoduleTensor.associatorIso_hom_value_eval,
    BimoduleTensor.leftBimoduleUnitIso_hom_value, BimoduleTensor.composeMap_value_eval]
  exact dgTensorLeftUnit_associator_value A B C E P Q b e

/-- 元の逆結合同型に沿って各因子の左単位を消しても、同じ合成の左単位を得る。 -/
lemma dgTensorLeftUnit_associator_inv :
    (BimoduleTensor.associatorIso A B B C E (Bimodule.diagonal A B) P Q).inv ≫
        BimoduleTensor.composeMap A B C E
          (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
          (𝟙 (BimoduleCategory.of A C E Q)) =
      (BimoduleTensor.leftBimoduleUnitIso A B E (BimoduleTensor.compose A B C E P Q)).hom := by
  apply (cancel_epi
    (BimoduleTensor.associatorIso A B B C E (Bimodule.diagonal A B) P Q).hom).1
  rw [Iso.hom_inv_id_assoc]
  exact (dgTensorLeftUnit_associator A B C E P Q).symm

end SerrePositivity.KST.SConstruction
