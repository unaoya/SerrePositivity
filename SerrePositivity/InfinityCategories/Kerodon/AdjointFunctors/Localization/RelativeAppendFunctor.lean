module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendObjects

/-!
# 元の相対関手と連結関手の全縦射の照合

概要：元の相対関手の適用は全連結関手と厳密に可換である。
方針：全縦成分の端点移送に関手を適用し、元の対象と全射を照合する。
規約：接合点の元の縦射を保持する。
使われ方：元の graph の合成と余極限上の合成の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

omit [V.IsMultiplicative] in
lemma append_app_heq {S S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {T T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z}
    (f : S ⟶ S') (g : T ⟶ T') (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) :
    HEq (F.functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app f g j))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F g) j) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app]
  split_ifs <;> simp only [F.functor.map_comp, eqToHom_map,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] <;> rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.append_app_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_app_heq)


omit [V.IsMultiplicative] in
lemma append_map_heq {S S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {T T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z}
    (f : S ⟶ S') (g : T ⟶ T') :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendMorphisms.map f g)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendObjects.append_obj F S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendObjects.append_obj F S' T') _ _ (append_app_heq F f g)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.append_map_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_map_heq)


lemma append_functor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) (X := X) (Y := Z) F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := a) (X := X) (Y := Y) F).prod
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := b) (X := Y) (Y := Z) F) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor := by
  apply CategoryTheory.Functor.hext (fun p => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendObjects.append_obj F p.1 p.2)
  intro p q f
  exact append_map_heq F f.1 f.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.append_functor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_functor)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
