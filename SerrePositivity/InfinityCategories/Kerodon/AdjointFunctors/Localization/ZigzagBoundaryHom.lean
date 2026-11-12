module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment

/-!
# 元の接合点の射を保持する境界付き縦射

概要：元の接合点の指定射と全縦成分の対応を保つ。
方針：先頭成分だけを固定し、全列の正方形と元の端点移送を回収する。
規約：接合点の指定射を恒等射とは仮定しない。
使われ方：DK9.4・10.3の元の語の Grothendieck 分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : C}
structure BoundaryHom {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} (f : X ⟶ X')
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X' Y) where
  hom : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T
  first : hom.app 0 = eqToHom S.first ≫ f ≫ eqToHom T.first.symm
  last : hom.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).length) = eqToHom (S.last.trans T.last.symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.BoundaryHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (BoundaryHom)


omit [W.IsMultiplicative] in
lemma BoundaryHom.ext {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} {f : X ⟶ X'}
    {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X' Y}
    (h k : BoundaryHom f S T) (hh : h.hom = k.hom) : h = k := by
  cases h
  cases k
  cases hh
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
