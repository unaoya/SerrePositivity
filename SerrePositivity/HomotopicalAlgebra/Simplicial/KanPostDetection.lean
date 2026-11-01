module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# Kan対象間の射の局所化可逆性を二つの後合成テストで判定する

## 概要
Kan対象間の射の局所化可逆性を二つの後合成テストで判定する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0427][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0427
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Two postcomposition tests detect localized equivalences between Kan objects
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanPostDetection
variable {X Y : SSet.{v}} (f : X ⟶ Y)
  (hX : SSet.modelCategoryQuillen.J.rlp (terminal.from X))
  (hY : SSet.modelCategoryQuillen.J.rlp (terminal.from Y))

include hX hY in
/-- Kan対象間の射の局所化可逆性を二つの後合成テストで判定する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。
-/
lemma localized_isIso
    (hs : Function.Surjective (HomotopyClasses.post f (X := Y)))
    (hi : Function.Injective (HomotopyClasses.post f (X := X))) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  obtain ⟨r, hr⟩ := hs (HomotopyClasses.mk (𝟙 Y))
  obtain ⟨g, rfl⟩ := Quot.exists_rep r
  have hgf : HomotopyClasses.mk (g ≫ f) = HomotopyClasses.mk (𝟙 Y) := hr
  have hfg : HomotopyClasses.mk (f ≫ g) = HomotopyClasses.mk (𝟙 X) := hi (by
    change HomotopyClasses.mk ((f ≫ g) ≫ f) = HomotopyClasses.mk (𝟙 X ≫ f)
    rw [Category.assoc, Category.id_comp]
    have h := congrArg (HomotopyClasses.pre f) hgf
    simpa only [HomotopyClasses.pre_mk, Category.comp_id] using h)
  obtain ⟨Hfg⟩ := KanActualHomotopy.of_class_eq hX hfg
  obtain ⟨Hgf⟩ := KanActualHomotopy.of_class_eq hY hgf
  let Q := AnodyneHomotopy.anodyneQ.{v}
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  exact ⟨⟨Q.map g,
    (Q.map_comp _ _).symm.trans
      ((AnodyneHomotopy.map_homotopy_eq Q hQ Hfg).trans (Q.map_id _)),
    (Q.map_comp _ _).symm.trans
      ((AnodyneHomotopy.map_homotopy_eq Q hQ Hgf).trans (Q.map_id _))⟩⟩

end SerrePositivity.SimplicialModel.KanPostDetection
