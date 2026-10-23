module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMappingProductMaps

/-!
概要：Tamme Remark 6 の写像空間の引き戻し正方形。
方針：元の右写像空間の引き戻しを二つの直積同型で輸送する。
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
/-- 概要：Tamme Remark 6 の写像空間の引き戻し正方形。
方針：元の右写像空間の引き戻しを二つの直積同型で輸送する。
規約：下辺は元の p・q が誘導する二射の直積。
使われ方：対象間写像空間のホモトピー引き戻しの表示。 -/
lemma laxPullbackMappingProduct_isPullback :
    IsPullback (pinchedHomMap (laxPullbackArrow p q) x y)
      (laxPullbackMappingProjections p q x y) (laxPullbackMappingEndpointMap p q x y)
      (pinchedHomMap p ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
          ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗ₘ
        pinchedHomMap q ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
          ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)) := by
  refine (pinchedHom_pullback_isPullback (arrowEndpointPair C) (p ⊗ₘ q) x y).of_iso
    (Iso.refl _) (Iso.refl _) (laxPullbackMappingInputsIso p q x y)
    (laxPullbackMappingBaseIso p q x y) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simpa only [Iso.refl_hom, Category.id_comp] using laxPullbackMappingProjections_eq p q x y
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · exact laxPullbackMappingBaseIso_rectangle p q x y
/-- 概要：Tamme Remark 6 の写像空間の引き戻し正方形。
方針：元の右写像空間の引き戻しを二つの直積同型で輸送する。
規約：下辺は元の p・q が誘導する二射の直積。
使われ方：対象間写像空間のホモトピー引き戻しの表示。 -/
instance laxPullbackMappingEndpointMap_fibration [Quasicategory C] :
    Fibration (laxPullbackMappingEndpointMap p q x y) := by
  dsimp only [laxPullbackMappingEndpointMap]
  infer_instance

end SerrePositivity.InfinityCategories.F2
