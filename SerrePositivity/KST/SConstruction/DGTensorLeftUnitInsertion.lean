module
public import SerrePositivity.KST.SConstruction.DGDiagonalUnitInsertion

/-! # 逆単位と結合を元の coend 包含射で比較する
概要：左端の単位を消す経路と、結合後に単位を消す経路の一致を示す。
方針：coend 包含、自由単位挿入の自然性、tensor の結合同型を合成する。
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

/-- coend の各包含上で、各因子への逆単位は元の自由単位挿入となる。 -/
lemma dgTensorLeftUnit_inverse_iota (b : B) (c : C) (e : E) :
    BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c ≫
        BimoduleTensor.composeValueMap A B C E
          (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
          (𝟙 (BimoduleCategory.of A C E Q)) b e =
      (Q.value c e ◁ dgDiagonalUnitInsertion A B (P.rightAt c) b) ≫
        BalancedTensor.ι A C (Q.rightAt e)
          ((BimoduleTensor.compose A B B C (Bimodule.diagonal A B) P).leftAt b) c := by
  have h := BimoduleTensor.ι_composeValueMap A B C E
    (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
    (𝟙 (BimoduleCategory.of A C E Q)) b c e
  rw [CategoryTheory.Functor.map_id, BimoduleTensor.leftBimoduleUnitIso_inv_value] at h
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at h
  change _ = (𝟙 (Q.value c e) ⊗ₘ
    (BalancedTensor.leftUnitValueIso A B (P.rightAt c) b).inv) ≫ _ at h
  rw [← dgDiagonalUnitInsertion_eq_inv A B (P.rightAt c) b, id_tensorHom] at h
  exact h

/-- 元の coend 包含上で、逆単位・結合は合成双加群への同じ挿入を回収する。 -/
lemma dgTensorLeftUnit_inverse_associator_iota (b : B) (c : C) (e : E) :
    BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c ≫
        BimoduleTensor.composeValueMap A B C E
          (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
          (𝟙 (BimoduleCategory.of A C E Q)) b e ≫
        (BimoduleTensor.associatorValueIso A B B C E (Bimodule.diagonal A B) P Q b e).hom =
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c ≫
        dgDiagonalUnitInsertion A B ((BimoduleTensor.compose A B C E P Q).rightAt e) b := by
  rw [← Category.assoc, dgTensorLeftUnit_inverse_iota]
  have ha := congrArg (fun k =>
    (Q.value c e ◁ freeUnitInsert A b (P.value b c)) ≫ k)
    (BimoduleTensor.associatorLeftι_hom A B B C E (Bimodule.diagonal A B) P Q b b c e)
  dsimp only [dgDiagonalUnitInsertion, BimoduleTensor.associatorLeftι] at ha ⊢
  simp only [whiskerLeft_comp, Category.assoc] at ha ⊢
  erw [ha]
  dsimp only [BimoduleTensor.associatorRightι, BalancedTensor.Fubini.rightι]
  rw [← Category.assoc]
  erw [dgFreeUnitInsert_tensor A B b (Q.value c e) (P.value b c)]
  have hn := freeUnitInsert_naturality A B b
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c)
  rw [tensorHom_id] at hn
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ BalancedTensor.ι A B
      ((BimoduleTensor.compose A B C E P Q).rightAt e)
      ((Bimodule.diagonal A B).leftAt b) b) hn).trans (Category.assoc _ _ _))

end SerrePositivity.KST.SConstruction
