module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackMappingProductMaps

/-!
概要：Tamme Remark 6 の写像空間の引き戻し正方形。
方針：元の右写像空間の引き戻しを二つの直積同型で輸送する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。

対応節は Kerodon 5.5（Tag 01YV）。
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
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌)
/-- 概要：Tamme Remark 6 の写像空間の引き戻し正方形。
方針：元の右写像空間の引き戻しを二つの直積同型で輸送する。
規約：下辺は元の p・q が誘導する二射の直積。
使われ方：対象間写像空間のホモトピー引き戻しの表示。 -/
lemma laxPullbackMappingProduct_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q) x y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingProjections p q x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingEndpointMap p q x y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)) := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pinchedHom_pullback_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q) x y).of_iso
    (Iso.refl _) (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingInputsIso p q x y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingBaseIso p q x y) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simpa only [Iso.refl_hom, Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingProjections_eq p q x y
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingBaseIso_rectangle p q x y
/-- 概要：Tamme Remark 6 の写像空間の引き戻し正方形。
方針：元の右写像空間の引き戻しを二つの直積同型で輸送する。
規約：下辺は元の p・q が誘導する二射の直積。
使われ方：対象間写像空間のホモトピー引き戻しの表示。 -/
instance laxPullbackMappingEndpointMap_fibration [Quasicategory C] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingEndpointMap p q x y) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingEndpointMap]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Eq (7)"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingProduct_isPullback
attribute [cite Tamme "Rem 6"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingProduct_isPullback
