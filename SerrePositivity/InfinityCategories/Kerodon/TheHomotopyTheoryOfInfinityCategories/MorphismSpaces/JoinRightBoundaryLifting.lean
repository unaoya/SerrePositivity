module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinRightBoundaryCorner
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：部分パラメータの join と右因子上の図式を同時に保つ関手の延長。
方針：相対境界の単射に沿う制限の持ち上げ性を、pushout の内部 Hom の引き戻しで記述する。
規約：相対境界への制限に対する持ち上げ性を仮定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、部分族の逆の選択と固定終点を両立する相対延長。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：join 図式の族は部分パラメータと右因子上の指定を同時に保って延長できる。
方針：二つの指定を内部 Hom の引き戻しで相対境界へ貼り、前合成の持ち上げ性を使う。
規約：標的の quasicategory 性や i,e の単射性はこの一般形には不要。
使われ方：Kerodon §4.6.6（Tag 04HY）、左 pinched 模型の比較の厳密な左逆の構成。 -/
lemma exists_joinDiagramFamily_extension_of_rightBoundary_of_hasLiftingProperty
    {E F A B X : SSet.{u}} (e : E ⟶ F) (i : A ⟶ B) (K : SSet.{u})
    [HasLiftingProperty e ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap i K)).app X)]
    (u : E ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K B)).obj X)
    (v : F ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A)).obj X) (w : F ⟶ (ihom B).obj X)
    (hv : e ≫ v = u ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) i)).app X)
    (hw : e ≫ w = u ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K B)).app X)
    (hvw : v ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A)).app X = w ≫ (pre i).app X) :
    ∃ U : F ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K B)).obj X,
      e ≫ U = u ∧ U ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) i)).app X = v ∧
        U ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K B)).app X = w := by
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryObject i K
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap i K
  let l := pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A) i
  let r := pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A) i
  let hp : IsPullback ((pre r).app X) ((pre l).app X)
      ((pre i).app X) ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A)).app X) :=
    (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A) i).op.map (internalHom.flip.obj X)
  let W : F ⟶ (ihom D).obj X := hp.lift w v hvw.symm
  have hWl : W ≫ (pre l).app X = v := hp.lift_snd _ _ _
  have hWr : W ≫ (pre r).app X = w := hp.lift_fst _ _ _
  have hjl : (pre j).app X ≫ (pre l).app X = (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) i)).app X := by
    rw [← NatTrans.comp_app, ← pre_map]
    exact congrArg (fun f ↦ (pre f).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_join i K)
  have hjr : (pre j).app X ≫ (pre r).app X = (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K B)).app X := by
    rw [← NatTrans.comp_app, ← pre_map]
    exact congrArg (fun f ↦ (pre f).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_right i K)
  have hsq : CommSq u e ((pre j).app X) W := by
    constructor
    apply hp.hom_ext
    · change (u ≫ (pre j).app X) ≫ (pre r).app X = (e ≫ W) ≫ (pre r).app X
      rw [Category.assoc, hjr, Category.assoc, hWr]
      exact hw.symm
    · change (u ≫ (pre j).app X) ≫ (pre l).app X = (e ≫ W) ≫ (pre l).app X
      rw [Category.assoc, hjl, Category.assoc, hWl]
      exact hv.symm
  refine ⟨hsq.lift, hsq.fac_left, ?_, ?_⟩
  · rw [← hjl, ← Category.assoc, hsq.fac_right, hWl]
  · rw [← hjr, ← Category.assoc, hsq.fac_right, hWr]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
