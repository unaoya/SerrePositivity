module

public import SerrePositivity.InfinityCategories.F2.LaxPullbackMappingProducts

/-!
概要：lax pullback の直積表示と p・q による後合成の整合。
方針：全次数の pinched 単体の元の値を比較する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (laxPullback p q) _⦋0⦌)
/-- 概要：lax pullback の直積表示と p・q による後合成の整合。
方針：全次数の pinched 単体の元の値を比較する。
規約：元の頂点と右写像空間の単体の値を保持する。
使われ方：原典の写像空間の四角形への厳密な輸送。 -/
lemma laxPullbackMappingBaseIso_rectangle :
    pinchedHomPullbackBaseMap (arrowEndpointPair C) (p ⊗ₘ q) x y ≫
      (laxPullbackMappingBaseIso p q x y).hom =
    (laxPullbackMappingInputsIso p q x y).hom ≫
      (pinchedHomMap p ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
          ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗ₘ
        pinchedHomMap q ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
          ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext <;> apply PinchedHom.Simplex.ext
  · change (((pinchedHomIsoOfEq _ _).hom.app (Opposite.op ⦋n⦌)
      ((pinchedHomPullbackBaseMap (arrowEndpointPair C) (p ⊗ₘ q) x y).app
        (Opposite.op ⦋n⦌) s)).val).1 = _
    rw [pinchedHomIsoOfEq_hom_val]
    rfl
  · change (((pinchedHomIsoOfEq _ _).hom.app (Opposite.op ⦋n⦌)
      ((pinchedHomPullbackBaseMap (arrowEndpointPair C) (p ⊗ₘ q) x y).app
        (Opposite.op ⦋n⦌) s)).val).2 = _
    rw [pinchedHomIsoOfEq_hom_val]
    rfl

end SerrePositivity.InfinityCategories.F2
