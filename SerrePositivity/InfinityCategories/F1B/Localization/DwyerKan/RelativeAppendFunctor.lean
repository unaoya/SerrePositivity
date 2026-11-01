module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeAppendObjects

/-!
# 元の相対関手と連結関手の全縦射の照合

概要：元の相対関手の適用は全連結関手と厳密に可換である。
方針：全縦成分の端点移送に関手を適用し、元の対象と全射を照合する。
規約：接合点の元の縦射を保持する。
使われ方：元の graph の合成と余極限上の合成の自然性。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Relative
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {a b : Word} {X Y Z : C}

omit [V.IsMultiplicative] in
lemma append_app_heq {S S' : Zigzag W a X Y} {T T' : Zigzag W b Y Z}
    (f : S ⟶ S') (g : T ⟶ T') (j : Fin ((Word.append a b).length + 1)) :
    HEq (F.functor.map (ZigzagAppend.app f g j))
      (ZigzagAppend.app (map F f) (map F g) j) := by
  dsimp only [ZigzagAppend.app]
  split_ifs <;> simp only [F.functor.map_comp, eqToHom_map,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] <;> rfl

omit [V.IsMultiplicative] in
lemma append_map_heq {S S' : Zigzag W a X Y} {T T' : Zigzag W b Y Z}
    (f : S ⟶ S') (g : T ⟶ T') :
    HEq (map F (ZigzagAppend.map f g)) (ZigzagAppend.map (map F f) (map F g)) :=
  Zigzag.hom_hext (append_obj F S T) (append_obj F S' T') _ _ (append_app_heq F f g)

lemma append_functor :
    ZigzagAppend.functor ⋙ functor (w := Word.append a b) (X := X) (Y := Z) F =
      (functor (w := a) (X := X) (Y := Y) F).prod
        (functor (w := b) (X := Y) (Y := Z) F) ⋙ ZigzagAppend.functor := by
  apply CategoryTheory.Functor.hext (fun p => append_obj F p.1 p.2)
  intro p q f
  exact append_map_heq F f.1 f.2

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
