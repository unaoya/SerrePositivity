module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt

/-!
# 元の端点の等式による zigzag 圏の移送

概要：端点の表示だけを等式で移し、元の全頂点・全列・全縦射を保持する。
方針：first/last の証明に端点の等式を合成し、射の成分を変更しない。
規約：恒等・合成則は厳密な等式。端点の同型の選択は追加しない。
使われ方：自由相対解像の固定対象の hammock 図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y X' Y' X'' Y'' : C}

def obj (hX : X = X') (hY : Y = Y') (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y' :=
  { S with first := S.first.trans hX, last := S.last.trans hY }

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.EndpointChange.obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange (obj)


def map (hX : X = X') (hY : Y = Y') {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (obj hX hY S) (obj hX hY T) :=
  ⟨f.app, f.app_mem, f.first, f.last, f.comm⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.EndpointChange.map export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange (map)


def functor (hX : X = X') (hY : Y = Y') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y' where
  obj := obj hX hY
  map := map hX hY
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (fun _ => rfl)
  map_comp _ _ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (fun _ => rfl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.EndpointChange.functor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange (functor)


lemma functor_refl : functor (W := W) (w := w) (rfl : X = X) (rfl : Y = Y) = 𝟭 _ := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.EndpointChange.functor_refl export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange (functor_refl)


lemma functor_comp (hX : X = X') (hY : Y = Y') (hX' : X' = X'') (hY' : Y' = Y'') :
    functor (W := W) (w := w) hX hY ⋙ functor hX' hY' =
      functor (hX.trans hX') (hY.trans hY') := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.EndpointChange.functor_comp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange (functor_comp)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange
