module

public import SerrePositivity.EInfinity.Hammock.ZigzagValuePath

/-!
# 元の全縦射による zigzag の値の不変性

概要：元の全縦射は値の射列の自然変換を与え、両端固定なら元の値を保つ。
方針：後ろ向きの列の可換正方形を反転し、全射列と端点の等式を回収する。
規約：全縦射を保持する。対象のモデル構造や局所化の飽和性は要求しない。
使われ方：各 hammock graph から通常の局所化 Hom の定数単体集合への評価。
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
  {w : Word} {X Y : C} {S T : Zigzag W w X Y}

lemma edge_comm (f : S ⟶ T) (i : Fin w.length) :
    edge L hL S i ≫ L.map (f.app i.succ) = L.map (f.app i.castSucc) ≫ edge L hL T i := by
  cases hi : w.direction i with
  | forward =>
    rw [edge_forward L hL S i hi, edge_forward L hL T i hi,
      ← L.map_comp, ← L.map_comp]
    exact congrArg L.map (Segment.forward_arrow_comm f i hi)
  | backward =>
    rw [edge_backward L hL S i hi, edge_backward L hL T i hi]
    have hc : (backwardIso L hL S i hi).hom ≫ L.map (f.app i.castSucc) =
        L.map (f.app i.succ) ≫ (backwardIso L hL T i hi).hom := by
      change L.map (Direction.arrow .backward S i hi).unop ≫ L.map (f.app i.castSucc) =
        L.map (f.app i.succ) ≫ L.map (Direction.arrow .backward T i hi).unop
      rw [← L.map_comp, ← L.map_comp]
      exact congrArg L.map (Segment.backward_arrow_comm f i hi)
    apply (cancel_epi (backwardIso L hL S i hi).hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

def pathMap (f : S ⟶ T) : path L hL S ⟶ path L hL T :=
  ComposableArrows.homMk (fun j => L.map (f.app j)) (by
    intro i hi
    dsimp only [path]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
    exact edge_comm L hL f ⟨i, hi⟩)

lemma value_eq (f : S ⟶ T) : value L hL S = value L hL T := by
  have hc := (pathMap L hL f).naturality
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  change (path L hL S).hom ≫ L.map (f.app (Fin.last w.length)) =
    L.map (f.app 0) ≫ (path L hL T).hom at hc
  rw [f.last, f.first, eqToHom_map, eqToHom_map] at hc
  have h := congrArg (fun k => eqToHom (congrArg L.obj S.first.symm) ≫ k ≫
    eqToHom (congrArg L.obj T.last)) hc
  simpa only [value, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using h

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
