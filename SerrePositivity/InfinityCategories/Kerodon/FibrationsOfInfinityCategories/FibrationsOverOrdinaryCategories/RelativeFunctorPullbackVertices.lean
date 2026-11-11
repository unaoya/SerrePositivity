module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyVertices

/-!
概要：相対写像空間の底変換の通常の射での計算。
方針：相対 curry の頂点公式と引き戻しの二射影を使う。
規約：可換性は厳密な等式であり、充填性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、底変換の豊穣作用と通常の底上の射の整合性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底変換は底上の射の相対頂点をその引き戻しの射の相対頂点へ写す。
方針：パラメーターを元の射の頂点に固定し、引き戻しの二成分を比較する。
規約：引き戻した射は第一射影と元の射の合成から持ち上げる。
使われ方：Kerodon §5.3.1（Tag 035D）、底変換関手の零次での作用の同定。 -/
lemma relativeFunctorPullback_vertex {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p q k).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q p f hf) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd q k) (pullback.snd p k)
      (pullback.lift (pullback.fst p k ≫ f) (pullback.snd p k)
        (by rw [Category.assoc, hf, pullback.condition])) (pullback.lift_snd _ _ _) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorCurry_vertex]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.parameterVertex_naturality, Category.assoc]
    congr 1
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
      ← Category.assoc, lift_fst, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
