module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagExt
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# 相対関手による元の固定語の zigzag の写像

概要：指定する矢を保つ元の関手を、同じ語の全対象と全縦射へ適用する。
方針：元の全頂点と全列を関手で送り、端点と可換性を元の関手の法則で移す。
規約：指定矢の類の乗法性だけを要求する。モデル構造は不要。
使われ方：自由相対解像から元の hammock への比較。
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
  (F : LocalizerMorphism W V) {w : Word} {X Y : C}

def obj (S : Zigzag W w X Y) : Zigzag V w (F.functor.obj X) (F.functor.obj Y) where
  vertex j := F.functor.obj (S.vertex j)
  first := congrArg F.functor.obj S.first
  last := congrArg F.functor.obj S.last
  arrow j := F.functor.map (S.arrow j)
  backward_mem j hj := F.map _ (S.backward_mem j hj)

def map {S T : Zigzag W w X Y} (f : Hom S T) : Hom (obj F S) (obj F T) where
  app j := F.functor.map (f.app j)
  app_mem j := F.map _ (f.app_mem j)
  first := by
    rw [f.first, eqToHom_map]
  last := by
    rw [f.last, eqToHom_map]
  comm j := by
    change F.functor.map (S.arrow j) ≫ F.functor.map (f.app (w.target j)) =
      F.functor.map (f.app (w.source j)) ≫ F.functor.map (T.arrow j)
    rw [← F.functor.map_comp, ← F.functor.map_comp, f.comm]

def functor : Zigzag W w X Y ⥤ Zigzag V w (F.functor.obj X) (F.functor.obj Y) where
  obj := obj F
  map := map F
  map_id _ := hom_ext _ _ (fun _ => F.functor.map_id _)
  map_comp _ _ := hom_ext _ _ (fun _ => F.functor.map_comp _ _)

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
