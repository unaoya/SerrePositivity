module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathSegmentMarked

/-!
# 元の forward 区間の非指定文字列と内部一列

概要：元の区間の文字列を内部一列の前後の元の合成の文字列へ分解する。
方針：元の三分割と射列の消去の合成則を使う。
規約：元の全生成矢と端点の移送を保持する。
使われ方：圧縮後の最初の非指定生成矢と元の同じ矢の照合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} (S : Zigzag W.paths w X Y)

lemma erase_forward_arrow (i : Fin w.length) (hi : w.direction i = .forward) :
    GeneratorWord.erase W (Direction.arrow .forward S i hi) = column W S i := by
  let hs : S.vertex i.castSucc = S.vertex (w.source i) :=
    congrArg S.vertex (by simp [Word.source, hi])
  let ht : S.vertex (w.target i) = S.vertex i.succ :=
    congrArg S.vertex (by simp [Word.target, hi])
  change GeneratorWord.erase W (Quiver.Path.comp
    (eqToHom hs : (S.vertex i.castSucc : Paths C) ⟶ S.vertex (w.source i))
    (Quiver.Path.comp (S.arrow i)
      (eqToHom ht : (S.vertex (w.target i) : Paths C) ⟶ S.vertex i.succ))) = _
  simp only [GeneratorWord.erase_comp, GeneratorWord.erase_eqToHom,
    List.nil_append, List.append_nil, column]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
namespace SerrePositivity.EInfinity.Hammock.Segment
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} (S : Zigzag W.paths w X Y)
  (p q : Fin (w.length + 1)) (hpq : p ≤ q)
  (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward)
  (i : Fin w.length) (hp : p.val ≤ i.val) (hq : i.val < q.val)

lemma erase_forward_map_split : GeneratorWord.erase W (map .forward S p q hpq hd) =
    GeneratorWord.erase W (map .forward S p i.castSucc (by exact hp)
      (fun j hj hj' => hd j hj (by change j.val < i.val at hj'; omega))) ++
    UnmarkedGenerators.column W S i ++
    GeneratorWord.erase W (map .forward S i.succ q (by change i.val + 1 ≤ q.val; omega)
      (fun j hj hj' => hd j (by change i.val + 1 ≤ j.val at hj; omega) hj')) := by
  rw [forward_map_split_column S p q hpq hd i hp hq]
  change GeneratorWord.erase W (Quiver.Path.comp _ (Quiver.Path.comp _ _)) = _
  simp only [GeneratorWord.erase_comp, UnmarkedGenerators.erase_forward_arrow, List.append_assoc]

end SerrePositivity.EInfinity.Hammock.Segment
