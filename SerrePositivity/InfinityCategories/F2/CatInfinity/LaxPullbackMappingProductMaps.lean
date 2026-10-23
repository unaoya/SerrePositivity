module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMappingProductNaturality

/-!
概要：原典の正方形の二射影と両端評価による写像。
方針：右写像空間を直積へ分け、底の端点の等式で輸送する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (laxPullback p q) _⦋0⦌)
/-- 概要：原典の正方形の二射影と両端評価による写像。
方針：右写像空間を直積へ分け、底の端点の等式で輸送する。
規約：下辺は元の p・q が誘導する二射の直積。
使われ方：対象間写像空間のホモトピー引き戻しの表示。 -/
def laxPullbackMappingProjections : pinchedHom x y ⟶
    pinchedHom ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
        ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗
      pinchedHom ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
        ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y) :=
  CartesianMonoidalCategory.lift (pinchedHomMap (laxPullbackFst p q) x y)
    (pinchedHomMap (laxPullbackSnd p q) x y)
/-- 概要：原典の正方形の二射影と両端評価による写像。
方針：右写像空間を直積へ分け、底の端点の等式で輸送する。
規約：下辺は元の p・q が誘導する二射の直積。
使われ方：対象間写像空間のホモトピー引き戻しの表示。 -/
def laxPullbackMappingEndpointMap :
    pinchedHom ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)
      ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) y) ⟶
    pinchedHom (p.app (Opposite.op ⦋0⦌) ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))
        (p.app (Opposite.op ⦋0⦌) ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y)) ⊗
      pinchedHom (q.app (Opposite.op ⦋0⦌) ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))
        (q.app (Opposite.op ⦋0⦌) ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)) :=
  pinchedHomMap (arrowEndpointPair C) ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)
      ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) y) ≫
    (laxPullbackMappingBaseIso p q x y).hom
/-- 概要：原典の正方形の二射影と両端評価による写像。
方針：右写像空間を直積へ分け、底の端点の等式で輸送する。
規約：下辺は元の p・q が誘導する二射の直積。
使われ方：対象間写像空間のホモトピー引き戻しの表示。 -/
lemma laxPullbackMappingProjections_eq :
    pinchedHomMap (pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) x y ≫
      (laxPullbackMappingInputsIso p q x y).hom = laxPullbackMappingProjections p q x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext <;> apply PinchedHom.Simplex.ext <;> rfl

end SerrePositivity.InfinityCategories.F2
