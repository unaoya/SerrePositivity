module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportBaseChange

/-!
概要：二回の底変換の比較は、元の全空間へ射影すると合成した底変換の比較と一致する。
方針：同じ section の族の展開を二回計算し、under の関手の合成を使う。
規約：全パラメーターを保持し、比較 path の独立な代表を選ばない。
使われ方：分類 Hom の底変換比較を共有頂点の制限と整合させる。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- under の底変換の関手は、元の底の関手の合成を厳密に保つ。 -/
lemma cocartesianStrictTransportUnderPost_comp
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) :
    (Under.post l : Under a ⥤ Under (l.obj a)) ⋙ Under.post k =
      Under.post (l ⋙ k) := rfl

/-- 二回の元の比較と合成した底変換の比較は、元の全空間への全相対族として一致する。 -/
lemma cocartesianStrictTransportBaseChangeComponent_comp_uncurry_snd
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    {E T : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (l : A ⥤ D) (k : D ⥤ C) (a : A)
    (s : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport p (k.obj (l.obj a))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (((s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k (l.obj a)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent (pullback.fst (nerveMap k) p) l a) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p))
          (nerveMap (Under.forget a))) ≫
        pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p) ≫ pullback.snd (nerveMap k) p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ((s ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p (l ⋙ k) a) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (pullback.fst (nerveMap (l ⋙ k)) p)
            (nerveMap (Under.forget a))) ≫ pullback.snd (nerveMap (l ⋙ k)) p := by
  rw [← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_uncurry_snd
      (pullback.fst (nerveMap k) p) l a
      (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k (l.obj a)),
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_uncurry_snd p k (l.obj a) s,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_uncurry_snd p (l ⋙ k) a s,
    ← Category.assoc,
    ← comp_whiskerRight]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
