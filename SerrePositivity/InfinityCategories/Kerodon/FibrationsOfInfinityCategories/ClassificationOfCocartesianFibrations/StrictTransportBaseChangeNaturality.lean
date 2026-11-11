module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportUnderPost

/-!
概要：strict transport の底変換の実際の成分を、全対象の自然変換へ束ねる。
方針：元の section の pullback 同型の自然性と under の厳密な正方形を使う。
規約：構成済みの同じ成分を使い、各底変換の元の全空間を標的とする。
使われ方：元の分類写像のセル制限の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
  (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (k : D ⥤ C)

/-- 元の底変換成分は、底の全ての射に対して厳密に自然。 -/
lemma cocartesianStrictTransportBaseChangeComponent_naturality {d e : D} (f : d ⟶ e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap p (k.map f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k e =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k d ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap (pullback.fst (nerveMap k) p) f := by
  let I (d : D) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso
    (IsPullback.of_hasPullback (nerveMap k) p).flip (nerveMap (Under.forget d))
    (nerveMap (Under.forget d) ≫ nerveMap k) rfl
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap (pullback.fst (nerveMap k) p) f ≫ (I e).hom =
      (I d).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p ((Over.map (nerveMap k)).map
        (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f) :
          Over.mk (nerveMap (Under.forget e)) ⟶ Over.mk (nerveMap (Under.forget d)))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso_pre (IsPullback.of_hasPullback (nerveMap k) p).flip
      (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f) :
        Over.mk (nerveMap (Under.forget e)) ⟶ Over.mk (nerveMap (Under.forget d)))
  apply (cancel_mono (I e).hom).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_iso,
    Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_iso]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportUnderPost_square]

/-- 元の strict transport を底の関手で制限した図式から、実際の底変換の図式への自然変換。 -/
def cocartesianStrictTransportBaseChange :
    k ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram (pullback.fst (nerveMap k) p) where
  app d := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k d
  naturality {d e} f := cocartesianStrictTransportBaseChangeComponent_naturality p k f

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
