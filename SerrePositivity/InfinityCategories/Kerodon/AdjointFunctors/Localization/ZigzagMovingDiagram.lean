module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws

/-!
# 両端の評価対象も動く zigzag 図式

概要：局所 zigzag の両端を添字圏上の関手とし、全縦射とその合成則を保持する。
方針：元の MovingHom と両端の元の射への回収式を記録する。
規約：局所端点を定数図式に固定しない。
使われ方：任意の前後の語を残した中央列のモデル圏的置換。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable (D : Type u') [Category.{v'} D] (C : Type u) [Category.{v} C]
  (W : MorphismProperty C) [W.IsMultiplicative] (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (A B : D ⥤ C)

structure MovingDiagram where
  obj : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w (A.obj d) (B.obj d)
  map : ∀ {d d'} (_f : d ⟶ d'), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (obj d) (obj d')
  map_id : ∀ d, map (𝟙 d) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (obj d)
  map_comp : ∀ {d d' d''} (f : d ⟶ d') (g : d' ⟶ d''),
    map (f ≫ g) = (map f).comp (map g)
  first : ∀ {d d'} (f : d ⟶ d'), HEq ((map f).app 0) (A.map f)
  last : ∀ {d d'} (f : d ⟶ d'), HEq ((map f).app (Fin.last w.length)) (B.map f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (MovingDiagram)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
