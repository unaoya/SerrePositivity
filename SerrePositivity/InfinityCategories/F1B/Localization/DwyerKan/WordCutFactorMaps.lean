module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorColumns

/-!
# 元の語の射を内部切断の prefix・残りの語へ制限する

概要：切断列とその像を含む前後の語に元の同じ列の単調写像を制限する。
方針：prefix は元の像の番号、残りは像から切断列の像を引いた番号を使う。
規約：元の全方向を保持し、空 fiber の恒等列挿入を含む。
使われ方：切断因子の全図式と hammock 余極限の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor
open CategoryTheory

variable {a b : Word} (f : a ⟶ b) (i : Fin a.length)

def prefixOrderHom : Fin (prefixWord a i).length →o
    Fin (prefixWord b (f.orderHom i)).length where
  toFun k := ⟨(f.orderHom (prefixColumn a i k)).val, by
    have hm := f.orderHom.monotone (prefixColumn_le a i k)
    change (f.orderHom (prefixColumn a i k)).val < (f.orderHom i).val + 1
    exact Nat.lt_succ_of_le hm⟩
  monotone' k l hkl := f.orderHom.monotone (show prefixColumn a i k ≤ prefixColumn a i l from hkl)

def residualOrderHom : Fin (residualWord a i).length →o
    Fin (residualWord b (f.orderHom i)).length where
  toFun k := ⟨(f.orderHom (residualColumn a i k)).val - (f.orderHom i).val, by
    have hk := (f.orderHom (residualColumn a i k)).isLt
    have hi := (f.orderHom i).isLt
    change (f.orderHom (residualColumn a i k)).val - (f.orderHom i).val <
      1 + (b.length - (f.orderHom i).val - 1)
    omega⟩
  monotone' k l hkl := Nat.sub_le_sub_right
    (f.orderHom.monotone (show residualColumn a i k ≤ residualColumn a i l from
      Nat.add_le_add_left hkl _)) _

def prefixMap (hi : a.direction i = .forward) :
    prefixWord a i ⟶ prefixWord b (f.orderHom i) where
  orderHom := prefixOrderHom f i
  direction_eq k := by
    rw [prefix_direction b (f.orderHom i) ((f.direction_eq i).trans hi), prefix_direction a i hi]
    exact f.direction_eq (prefixColumn a i k)

def residualMap (hi : a.direction i = .forward) :
    residualWord a i ⟶ residualWord b (f.orderHom i) where
  orderHom := residualOrderHom f i
  direction_eq k := by
    rw [residual_direction b (f.orderHom i) ((f.direction_eq i).trans hi),
      residual_direction a i hi]
    have he : residualColumn b (f.orderHom i) (residualOrderHom f i k) =
        f.orderHom (residualColumn a i k) := by
      apply Fin.ext
      have hm := f.orderHom.monotone (le_residualColumn a i k)
      change (f.orderHom i).val +
        ((f.orderHom (residualColumn a i k)).val - (f.orderHom i).val) = _
      omega
    rw [he]
    exact f.direction_eq (residualColumn a i k)

end SerrePositivity.EInfinity.Hammock.Word.CutFactor
