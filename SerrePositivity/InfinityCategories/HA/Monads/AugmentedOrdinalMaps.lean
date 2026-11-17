module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fintype.Fin

/-!
概要：増大単体圏の射を、空も含む有限順序集合の実単調射として表示する。
方針：非空の対象では元のtoOrderHomを使い、空の対象の射を場合分けする。
規約：cardは点の個数であり、単体の次元とは1だけ異なる。
使われ方：HA Proposition 4.7.3.3 のwalking adjunctionの区間表示への包装。
Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：増大単体圏の対象の点の個数。
方針：空は0、非空は次元+1とする。規約：空の対象を別に扱う。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示。 -/
abbrev augmentedOrdinalCard : AugmentedSimplexCategory → ℕ
  | .star => 0
  | .of x => x.len + 1

/-- 概要：点の個数から同じ増大単体圏の対象を作る。
方針：0か後続数かで分ける。規約：指定された骨格の対象。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の対象の逆。 -/
def augmentedOrdinalOfCard : ℕ → AugmentedSimplexCategory
  | 0 => .star
  | n + 1 => .of (SimplexCategory.mk n)

/-- 概要：個数から作った対象は指定された点の個数を持つ。
方針：自然数を場合分けする。規約：空の場合も含む。
使われ方：Riehl–Verity Remark 3.3.8 の本質的全射性。 -/
@[simp] lemma augmentedOrdinalCard_ofCard (n : ℕ) :
    augmentedOrdinalCard (augmentedOrdinalOfCard n) = n := by
  cases n <;> rfl

/-- 概要：増大単体圏の射を実際の有限単調射にする。
方針：空を始域にする射は空写像、非空間の射は元のtoOrderHomを使う。
規約：空への非空からの射は存在しない。使われ方：Riehl–Verity Remark 3.3.8。 -/
def augmentedOrderHom {X Y : AugmentedSimplexCategory} (f : X ⟶ Y) :
    Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y) := by
  cases X with
  | star => exact ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  | of x =>
    cases Y with
    | star => exact PEmpty.elim f
    | of y => exact f.toOrderHom

/-- 概要：実有限単調射から増大単体圏の射を回収する。
方針：空の対象の場合を分け、非空間ではHom.mkを使う。
規約：空への不可能な写像はFin.elim0で除く。使われ方：Riehl–Verity Remark 3.3.8。 -/
def augmentedHomOfOrder (X Y : AugmentedSimplexCategory)
    (f : Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y)) : X ⟶ Y := by
  cases X with
  | star => cases Y <;> exact PUnit.unit
  | of x =>
    cases Y with
    | star => exact Fin.elim0 (f 0)
    | of y => exact SimplexCategory.Hom.mk f

/-- 概要：増大単体圏の射の表示・回収は元の射に戻る。
方針：空の射の一意性と非空の表示の定義を使う。規約：射の等式。
使われ方：Riehl–Verity Remark 3.3.8 の忠実性。 -/
lemma augmentedHomOfOrder_order {X Y : AugmentedSimplexCategory} (f : X ⟶ Y) :
    augmentedHomOfOrder X Y (augmentedOrderHom f) = f := by
  cases X with
  | star => cases Y <;> exact Subsingleton.elim _ _
  | of x => cases Y with
    | star => cases f
    | of y => rfl

/-- 概要：実有限単調射の回収・表示は元の単調射に戻る。
方針：空の始域では外延性、非空の場合は定義を使う。
規約：同じ有限順序集合上の射。使われ方：Riehl–Verity Remark 3.3.8 の充満性。 -/
lemma augmentedOrderHom_ofOrder (X Y : AugmentedSimplexCategory)
    (f : Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y)) :
    augmentedOrderHom (augmentedHomOfOrder X Y f) = f := by
  cases X with
  | star =>
    apply OrderHom.ext
    funext i
    exact Fin.elim0 i
  | of x => cases Y with
    | star => exact Fin.elim0 (f 0)
    | of y => rfl

/-- 概要：増大単体圏の射と有限単調射の実全単射。
方針：両方向の実構成と往復の等式をまとめる。
規約：空の対象も含む。使われ方：Riehl–Verity Remark 3.3.8 の区間表示のHom。 -/
def augmentedOrderHomEquiv (X Y : AugmentedSimplexCategory) :
    (X ⟶ Y) ≃ (Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y)) where
  toFun := augmentedOrderHom
  invFun := augmentedHomOfOrder X Y
  left_inv := augmentedHomOfOrder_order
  right_inv := augmentedOrderHom_ofOrder X Y

/-- 概要：増大単体圏の恒等射の表示は有限順序集合の恒等射。
方針：空の場合を外延性で処理する。規約：全対象を量化する。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の関手性。 -/
@[simp] lemma augmentedOrderHom_id (X : AugmentedSimplexCategory) :
    augmentedOrderHom (𝟙 X) = OrderHom.id := by
  cases X with
  | star =>
    apply OrderHom.ext
    funext i
    exact Fin.elim0 i
  | of x => rfl

/-- 概要：増大単体圏の合成の表示は有限単調射の合成。
方針：空への不可能な射を除き、空の始域では外延性で示す。
規約：元の射の向きを保つ。使われ方：Riehl–Verity Remark 3.3.8 の反変合成。 -/
@[simp] lemma augmentedOrderHom_comp {X Y Z : AugmentedSimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    augmentedOrderHom (f ≫ g) = (augmentedOrderHom g).comp (augmentedOrderHom f) := by
  cases X with
  | star =>
    apply OrderHom.ext
    funext i
    exact Fin.elim0 i
  | of x => cases Y with
    | star => cases f
    | of y => cases Z with
      | star => cases g
      | of z => rfl

end SerrePositivity.InfinityCategories.HA.Monads
