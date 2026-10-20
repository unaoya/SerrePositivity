module

public import SerrePositivity.EInfinity.Hammock.Zigzag
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# 相対関手による固定語の zigzag の後合成

概要：指定弱同値を保つ関手を全列・全縦射へ同時に作用させる。
方針：元の関手の射の像と合成則で全可換正方形を移す。
規約：両端点は同じ関手の対象の像であり、追加の置換を使わない。
使われ方：hammock の係数自然性と自由解像との比較。
-/

@[expose] public section
universe u v u' v'

namespace SerrePositivity.EInfinity.Hammock.Zigzag
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} {V : MorphismProperty D} (F : C ⥤ D)
  (hF : W ≤ V.inverseImage F) {w : Word} {X Y : C}

/-- 同じ語の全列と固定端点の元の関手による像。 -/
def postcomposeObj (S : Zigzag W w X Y) : Zigzag V w (F.obj X) (F.obj Y) where
  vertex j := F.obj (S.vertex j)
  first := congrArg F.obj S.first
  last := congrArg F.obj S.last
  arrow i := F.map (S.arrow i)
  backward_mem i hi := hF _ (S.backward_mem i hi)

/-- 元の全縦弱同値と可換正方形の像。 -/
def postcomposeMap {S T : Zigzag W w X Y} (f : Hom S T) :
    Hom (postcomposeObj F hF S) (postcomposeObj F hF T) where
  app j := F.map (f.app j)
  app_mem j := hF _ (f.app_mem j)
  first := by
    simp only [f.first, eqToHom_map]
    rfl
  last := by
    simp only [f.last, eqToHom_map]
    rfl
  comm i := by simpa only [postcomposeObj, F.map_comp] using congrArg F.map (f.comm i)

/-- 指定弱同値を保つ関手による固定語の zigzag 圏の関手。 -/
def postcompose [W.IsMultiplicative] [V.IsMultiplicative] :
    Zigzag W w X Y ⥤ Zigzag V w (F.obj X) (F.obj Y) where
  obj := postcomposeObj F hF
  map := postcomposeMap F hF
  map_id _ := hom_ext _ _ (fun _ => F.map_id _)
  map_comp _ _ := hom_ext _ _ (fun _ => F.map_comp _ _)

/-- 恒等関手は元の zigzag と全縦射を厳密に固定する。 -/
lemma postcompose_id [W.IsMultiplicative] :
    postcompose (W := W) (w := w) (X := X) (Y := Y) (𝟭 C) (fun _ _ _ h => h) =
      𝟭 (Zigzag W w X Y) := rfl

/-- 二つの相対関手の後合成は元の合成関手の後合成に厳密に一致。 -/
lemma postcompose_comp {E : Type*} [Category E] {U : MorphismProperty E}
    [W.IsMultiplicative] [V.IsMultiplicative] [U.IsMultiplicative]
    (G : D ⥤ E) (hG : V ≤ U.inverseImage G) :
    postcompose (w := w) (X := X) (Y := Y) F hF ⋙ postcompose G hG =
      postcompose (F ⋙ G) (fun _ _ f hf => hG _ (hF f hf)) := rfl

end SerrePositivity.EInfinity.Hammock.Zigzag
