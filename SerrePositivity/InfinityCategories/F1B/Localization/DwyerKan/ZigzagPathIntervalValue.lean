module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagIntervalValue

/-!
# 元の値の射列による同方向区間の評価の回収

概要：元の値の射列の区間射は、同じ向きの区間全体を評価した射に等しい。
方針：終点の番号で帰納し、空区間・元の隣接列・元の分割則を使う。
規約：区間の長さに正値性を仮定しない。
使われ方：元の WordAction の fiber を値の射列の制限と同定する。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {w : Word} {X Y : C}

omit [W.IsMultiplicative] in
lemma path_map_adjacent (S : Zigzag W w X Y) (i : Fin w.length) :
    (path L hL S).map (homOfLE (Fin.castSucc_le_succ i)) = edge L hL S i := by
  change (path L hL S).map' i.val (i.val + 1) = _
  dsimp only [path]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i.val i.isLt]

lemma path_interval (d : Direction) (S : Zigzag W w X Y)
    (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    (path L hL S).map (homOfLE hpq) = intervalValue L hL d S p q hpq hd := by
  induction q using Fin.induction generalizing p with
  | zero =>
    have he : p = 0 := le_antisymm hpq (Fin.zero_le _)
    subst p
    rw [intervalValue_refl]
    exact (path L hL S).map_id _
  | succ i ih =>
    have his : i.succ.val = i.val + 1 := rfl
    have hic : i.castSucc.val = i.val := rfl
    by_cases he : p = i.succ
    · subst p
      rw [intervalValue_refl]
      exact (path L hL S).map_id _
    · have hpi : p ≤ i.castSucc := by omega
      have hc : (path L hL S).map (homOfLE hpq) =
          (path L hL S).map (homOfLE hpi) ≫
            (path L hL S).map (homOfLE (Fin.castSucc_le_succ i)) :=
        (path L hL S).map_comp _ _
      rw [hc, ih p hpi (fun j hj hj' => hd j hj (by omega)), path_map_adjacent,
        intervalValue_comp L hL d S p i.castSucc i.succ hpi (Fin.castSucc_le_succ i) hd,
        intervalValue_adjacent L hL d S i (hd i (by omega) (by omega))]

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
