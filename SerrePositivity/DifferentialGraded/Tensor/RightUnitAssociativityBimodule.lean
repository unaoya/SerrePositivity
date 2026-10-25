module
public import SerrePositivity.DifferentialGraded.Tensor.RightUnitAssociativity
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.UnitMapNaturality
/-!
概要：右 Yoneda 単位と結合の値ごとの整合性を実双加群射の整合性へ束ねる。
方針：全値への評価の忠実性と既存の tensor 双関手を使う。
規約：元の実結合同型と単位同型を保持する。
使われ方：D-19 の graph 作用の代表上の合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C]
  [DGCategory A E] [Small.{u} E] (P : Bimodule A B C) (Q : Bimodule A C E)

lemma rightUnit_associator :
    (associatorIso A B C E E P Q (Bimodule.diagonal A E)).hom ≫
      composeMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (rightBimoduleUnitIso A C E Q).hom =
    (rightBimoduleUnitIso A B E (compose A B C E P Q)).hom := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  simp only [CategoryTheory.Functor.map_comp, associatorIso_hom_value_eval,
    composeMap_value_eval, rightBimoduleUnitIso_hom_value]
  exact rightUnit_associator_value A B C E P Q b e

lemma rightUnit_associator_inv :
    (associatorIso A B C E E P Q (Bimodule.diagonal A E)).inv ≫
      (rightBimoduleUnitIso A B E (compose A B C E P Q)).hom =
    composeMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (rightBimoduleUnitIso A C E Q).hom := by
  rw [← rightUnit_associator A B C E P Q, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
