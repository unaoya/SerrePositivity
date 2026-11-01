module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendMorphisms

/-!
# 固定語の zigzag の連結関手

概要：二つの元の固定語の zigzag 圏から連結語の zigzag 圏への関手を構成する。
方針：元の全頂点の縦射の合成と、端点の等式による移送を照合する。
規約：元の恒等・合成を厳密に保持し、共有端点の条件を追加仮定しない。
使われ方：固定語の graph の単体的合成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y Z : C}
  [W.IsMultiplicative]

/-- 連結の全頂点の縦射は、元の同じ恒等射を保持する。 -/
lemma app_id (S : Zigzag W a X Y) (T : Zigzag W b Y Z)
    (k : Fin ((Word.append a b).length + 1)) : app (𝟙 S) (𝟙 T) k = 𝟙 (vertex S T k) := by
  unfold app
  split_ifs <;> simp only [Zigzag.id_app, Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- 連結の全頂点の縦射は、元の同じ合成を保持する。 -/
lemma app_comp {S S' S'' : Zigzag W a X Y} {T T' T'' : Zigzag W b Y Z}
    (f : S ⟶ S') (g : T ⟶ T') (f' : S' ⟶ S'') (g' : T' ⟶ T'')
    (k : Fin ((Word.append a b).length + 1)) :
    app (f ≫ f') (g ≫ g') k = app f g k ≫ app f' g' k := by
  unfold app
  split_ifs <;> simp only [Zigzag.comp_app, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

/-- 元の全対象と全縦弱同値の連結関手。 -/
def functor : Zigzag W a X Y × Zigzag W b Y Z ⥤ Zigzag W (Word.append a b) X Z where
  obj p := obj p.1 p.2
  map f := map f.1 f.2
  map_id p := Zigzag.hom_ext _ _ (fun k => app_id p.1 p.2 k)
  map_comp f g := Zigzag.hom_ext _ _ (fun k => app_comp f.1 f.2 g.1 g.2 k)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
