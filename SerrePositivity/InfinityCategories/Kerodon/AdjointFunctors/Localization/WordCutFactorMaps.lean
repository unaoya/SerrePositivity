module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorColumns

/-!
# 元の語の射を内部切断の prefix・残りの語へ制限する

概要：切断列とその像を含む前後の語に元の同じ列の単調写像を制限する。
方針：prefix は元の像の番号、残りは像から切断列の像を引いた番号を使う。
規約：元の全方向を保持し、空 fiber の恒等列挿入を含む。
使われ方：切断因子の全図式と hammock 余極限の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps
open CategoryTheory

variable {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (i : Fin a.length)

def prefixOrderHom : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord a i).length →o
    Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b (f.orderHom i)).length where
  toFun k := ⟨(f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn a i k)).val, by
    have hm := f.orderHom.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn_le a i k)
    change (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn a i k)).val < (f.orderHom i).val + 1
    exact Nat.lt_succ_of_le hm⟩
  monotone' k l hkl := f.orderHom.monotone (show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn a i k ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn a i l from hkl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixOrderHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps (prefixOrderHom)


def residualOrderHom : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord a i).length →o
    Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord b (f.orderHom i)).length where
  toFun k := ⟨(f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k)).val - (f.orderHom i).val, by
    have hk := (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k)).isLt
    have hi := (f.orderHom i).isLt
    change (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k)).val - (f.orderHom i).val <
      1 + (b.length - (f.orderHom i).val - 1)
    omega⟩
  monotone' k l hkl := Nat.sub_le_sub_right
    (f.orderHom.monotone (show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i l from
      Nat.add_le_add_left hkl _)) _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualOrderHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps (residualOrderHom)


def prefixMap (hi : a.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord a i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b (f.orderHom i) where
  orderHom := prefixOrderHom f i
  direction_eq k := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_direction b (f.orderHom i) ((f.direction_eq i).trans hi), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_direction a i hi]
    exact f.direction_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixColumn a i k)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixMap export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps (prefixMap)


def residualMap (hi : a.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord a i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord b (f.orderHom i) where
  orderHom := residualOrderHom f i
  direction_eq k := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_direction b (f.orderHom i) ((f.direction_eq i).trans hi),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_direction a i hi]
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn b (f.orderHom i) (residualOrderHom f i k) =
        f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k) := by
      apply Fin.ext
      have hm := f.orderHom.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.le_residualColumn a i k)
      change (f.orderHom i).val +
        ((f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k)).val - (f.orderHom i).val) = _
      omega
    rw [he]
    exact f.direction_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i k)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualMap export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps (residualMap)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps
