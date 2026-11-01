module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerNaturality
public import Mathlib.Order.SuccPred.Nat

/-!
# 新しい次数の指定セルと既存の低次数の図式を自然な一つの低次数系に貼り合わせる

## 概要
新しい次数の指定セルと既存の低次数の図式を自然な一つの低次数系に貼り合わせる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0267][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0267
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Assemble independently prescribed new-degree cells into a natural lower system

Only incoming direct and outgoing inverse compatibility with the old
system is required. Unique Reedy factorization supplies naturality on all
other arrows, including arrows between distinct objects of the new degree.
No lifting, model structure or boundary limits are assumed here.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.PrescribedLowerStep
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  (F G : J ⥤ C) (n : ℕ) (old : lowerInclusion r n ⋙ F ⟶ lowerInclusion r n ⋙ G)

structure Data where
  hom (j : J) (hj : r.deg j = n) : F.obj j ⟶ G.obj j
  incoming (j : J) (hj : r.deg j = n) {x : Lower r n} (f : x.obj ⟶ j) (hf : direct f) :
    F.map f ≫ hom j hj = old.app x ≫ G.map f
  outgoing (j : J) (hj : r.deg j = n) {x : Lower r n} (f : j ⟶ x.obj) (hf : inverse f) :
    F.map f ≫ old.app x = hom j hj ≫ G.map f

namespace Data
variable {r F G n old} (d : Data r F G n old)

abbrev app (j : Lower r (n + 1)) : F.obj j.obj ⟶ G.obj j.obj :=
  if hj : r.deg j.obj < n then old.app ⟨j.obj, hj⟩
  else d.hom j.obj (le_antisymm (Nat.le_of_lt_succ j.property) (Nat.le_of_not_gt hj))

lemma naturality_direct {x y : Lower r (n + 1)} (f : x ⟶ y) (hf : direct f.hom) :
    F.map f.hom ≫ d.app y = d.app x ≫ G.map f.hom := by
  by_cases hy : r.deg y.obj < n
  · have hx := lt_of_le_of_lt (r.le₂ f.hom hf) hy
    rw [app, dite_eq_left hy, app, dite_eq_left hx]
    exact old.naturality (ObjectProperty.homMk f.hom : ⟨x.obj, hx⟩ ⟶ ⟨y.obj, hy⟩)
  · by_cases hid : MorphismProperty.identities J f.hom
    · exact naturality_on_lower_identities r (n + 1) d.app f hid
    · have hx := lt_of_lt_of_le (r.lt₂ f.hom hf hid) (Nat.le_of_lt_succ y.property)
      rw [app, dite_eq_right hy, app, dite_eq_left hx]
      exact d.incoming y.obj _ (x := ⟨x.obj, hx⟩) f.hom hf

lemma naturality_inverse {x y : Lower r (n + 1)} (f : x ⟶ y) (hf : inverse f.hom) :
    F.map f.hom ≫ d.app y = d.app x ≫ G.map f.hom := by
  by_cases hx : r.deg x.obj < n
  · have hy := lt_of_le_of_lt (r.le₁ f.hom hf) hx
    rw [app, dite_eq_left hy, app, dite_eq_left hx]
    exact old.naturality (ObjectProperty.homMk f.hom : ⟨x.obj, hx⟩ ⟶ ⟨y.obj, hy⟩)
  · by_cases hid : MorphismProperty.identities J f.hom
    · exact naturality_on_lower_identities r (n + 1) d.app f hid
    · have hy := lt_of_lt_of_le (r.lt₁ f.hom hf hid) (Nat.le_of_lt_succ x.property)
      rw [app, dite_eq_left hy, app, dite_eq_right hx]
      exact d.outgoing x.obj _ (x := ⟨y.obj, hy⟩) f.hom hf

/- 旧宣言の技術注記：
The actual natural transformation containing all old and newly specified cells.
-/
/-- 新しい次数の指定セルと既存の低次数の図式を自然な一つの低次数系に貼り合わせる。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。
-/
def assemble : lowerInclusion r (n + 1) ⋙ F ⟶ lowerInclusion r (n + 1) ⋙ G :=
  natTransOnLowerOfReedy r (n + 1) d.app d.naturality_inverse d.naturality_direct

lemma assemble_old (j : Lower r n) :
    d.assemble.app ⟨j.obj, lt_trans j.property (Nat.lt_succ_self n)⟩ = old.app j := by
  change d.app _ = _
  exact dite_eq_left j.property

lemma assemble_new (j : J) (hj : r.deg j = n) :
    d.assemble.app ⟨j, hj ▸ Nat.lt_succ_self n⟩ = d.hom j hj := by
  change d.app _ = _
  exact dite_eq_right (hj ▸ Nat.lt_irrefl n)

lemma assemble_restrict : Functor.whiskerLeft (lowerMap r (Nat.le_succ n)) d.assemble = old := by
  apply NatTrans.ext
  funext j
  exact d.assemble_old j

end Data
end SerrePositivity.Reedy.PrescribedLowerStep
