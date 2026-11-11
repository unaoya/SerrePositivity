module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportBaseChange

/-!
概要：under の関手は、底の射による under の前合成と厳密に可換。
方針：底の関手の合成保存を構造射に用い、射は under の忘却関手で比較する。
規約：自然同型ではなく、底上の射の等式。
使われ方：strict transport の底変換成分の厳密な自然性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- under の前合成と底の関手を作用させる順序を交換する。 -/
lemma cocartesianStrictTransportUnderPost_map
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (k : D ⥤ C) {d e : D} (f : d ⟶ e) :
    Under.post k ⋙ Under.map (k.map f) = Under.map f ⋙ Under.post k := by
  refine CategoryTheory.Functor.ext (fun a ↦ ?_) ?_
  · change Under.mk (k.map f ≫ k.map a.hom) = Under.mk (k.map (f ≫ a.hom))
    rw [k.map_comp]
  · intro a b h
    apply (Under.forget (k.obj d)).map_injective
    simp

/-- 同じ under の可換正方形は、元の底の nerve 上で厳密に可換。 -/
lemma cocartesianStrictTransportUnderPost_square
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (k : D ⥤ C) {d e : D} (f : d ⟶ e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportUnderPost k e ≫
      (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (k.map f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection (k.map f)) :
        Over.mk (nerveMap (Under.forget (k.obj e))) ⟶
          Over.mk (nerveMap (Under.forget (k.obj d)))) =
    (Over.map (nerveMap k)).map
      (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f) :
        Over.mk (nerveMap (Under.forget e)) ⟶ Over.mk (nerveMap (Under.forget d))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportUnderPost k d := by
  apply Over.OverMorphism.ext
  exact congrArg nerveMap (cocartesianStrictTransportUnderPost_map k f)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
