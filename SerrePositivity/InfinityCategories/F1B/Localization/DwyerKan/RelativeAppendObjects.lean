module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeZigzagFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendFunctor

/-!
# 元の相対関手と全 zigzag の連結の対象の照合

概要：元の相対関手の適用は元の連結の全対象・横列を保持する。
方針：接合点を共有する頂点列と左右の元の列の回収を使う。
規約：元の端点の等式とその関手像を保持する。
使われ方：相対関手による元の hammock 合成の保存。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Relative
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} {V : MorphismProperty D}
  (F : LocalizerMorphism W V) {a b : Word} {X Y Z : C}

lemma map_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    (p : A ⟶ B) (q : A' ⟶ B') (hp : HEq p q) : HEq (F.functor.map p) (F.functor.map q) := by
  cases hA
  cases hB
  cases eq_of_heq hp
  rfl

lemma append_obj (S : Zigzag W a X Y) (T : Zigzag W b Y Z) :
    obj F (ZigzagAppend.obj S T) = ZigzagAppend.obj (obj F S) (obj F T) := by
  apply Zigzag.object_ext
  · intro j
    change F.functor.obj (ZigzagAppend.vertex S T j) =
      ZigzagAppend.vertex (obj F S) (obj F T) j
    dsimp only [ZigzagAppend.vertex]
    split_ifs <;> rfl
  · intro j
    cases j using Fin.addCases with
    | left j =>
      exact (map_heq F (ZigzagAppend.source_left_eq S T j)
        (ZigzagAppend.target_left_eq S T j) _ _ (ZigzagAppend.arrow_left_heq S T j)).trans
          (ZigzagAppend.arrow_left_heq (obj F S) (obj F T) j).symm
    | right j =>
      exact (map_heq F (ZigzagAppend.source_right_eq S T j)
        (ZigzagAppend.target_right_eq S T j) _ _ (ZigzagAppend.arrow_right_heq S T j)).trans
          (ZigzagAppend.arrow_right_heq (obj F S) (obj F T) j).symm

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
