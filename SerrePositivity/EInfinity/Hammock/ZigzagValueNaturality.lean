module

public import SerrePositivity.EInfinity.Hammock.ZigzagValueMaps

/-!
# 反転関手の元の自然変換と zigzag 評価

概要：全語の評価は元の自然変換の両端成分と可換。
方針：前向きの自然性と後ろ向きの逆射の可換式を全射列へ束ねる。
規約：自然変換の成分の可逆性は要求しない。
使われ方：元の局所化の因子化同型を π₀ の評価へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} {L M : C ⥤ D} (hL : W.IsInvertedBy L) (hM : W.IsInvertedBy M)
  (η : L ⟶ M) {w : Word} {X Y : C} (S : Zigzag W w X Y)

lemma edge_naturality (i : Fin w.length) :
    edge L hL S i ≫ η.app (S.vertex i.succ) =
      η.app (S.vertex i.castSucc) ≫ edge M hM S i := by
  cases hi : w.direction i with
  | forward =>
    rw [edge_forward L hL S i hi, edge_forward M hM S i hi]
    exact η.naturality (Direction.arrow .forward S i hi)
  | backward =>
    rw [edge_backward L hL S i hi, edge_backward M hM S i hi]
    have h := η.naturality (Direction.arrow .backward S i hi).unop
    change (backwardIso L hL S i hi).hom ≫ η.app (S.vertex i.castSucc) =
      η.app (S.vertex i.succ) ≫ (backwardIso M hM S i hi).hom at h
    apply (cancel_epi (backwardIso L hL S i hi).hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

def pathNatTrans : path L hL S ⟶ path M hM S :=
  ComposableArrows.homMk (fun i => η.app (S.vertex i)) (by
    intro i hi
    simp only [path, ComposableArrows.mkOfObjOfMapSucc_map_succ]
    exact edge_naturality hL hM η S ⟨i, hi⟩)

lemma value_naturality : value L hL S ≫ η.app Y = η.app X ≫ value M hM S := by
  have h := (pathNatTrans hL hM η S).naturality
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  change (path L hL S).hom ≫ η.app (S.vertex (Fin.last _)) =
    η.app (S.vertex 0) ≫ (path M hM S).hom at h
  have hX := η.naturality (eqToHom S.first.symm)
  have hY := η.naturality (eqToHom S.last)
  simp only [eqToHom_map] at hX hY
  dsimp only [value]
  simp only [Category.assoc]
  rw [hY, ← Category.assoc (path L hL S).hom, h, Category.assoc,
    ← Category.assoc _ (η.app (S.vertex 0)), hX, Category.assoc]

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
