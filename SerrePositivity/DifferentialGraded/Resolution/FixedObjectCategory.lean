module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectAugmentation

/-! # 固定対象の豊穣構造を独立した対象型上の主dg圏へ戻す

## 概要
固定対象の豊穣構造を独立した対象型上の主dg圏へ戻す。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation
open CategoryTheory
variable {A : Type u} [CommRing A] {X : Type v} {E : Type w} [DGCategory A E] {o : X → E}

structure Objects (_S : FixedObjectAugmentation A X E o) where
  val : X

variable (S : FixedObjectAugmentation A X E o)

def objectEquiv : X ≃ S.Objects where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

instance objectsSmall [Small.{u} X] : Small.{u} S.Objects :=
  small_of_injective (f := fun x : S.Objects => x.val) (by
    rintro ⟨x⟩ ⟨y⟩ h
    cases h
    rfl)

instance objectsDGCategory : DGCategory A S.Objects :=
  ofHomObjects A S.Objects (fun x y => S.category.Hom x.val y.val)
    (fun x => S.category.id x.val) (fun x y z => S.category.comp x.val y.val z.val)
    (fun x y => S.category.id_comp x.val y.val)
    (fun x y => S.category.comp_id x.val y.val)
    (fun w x y z => S.category.assoc w.val x.val y.val z.val)

def augmentation : DGFunctor A S.Objects E where
  obj x := o x.val
  map x y := S.map x.val y.val
  map_id x := S.map_id x.val
  map_comp x y z := S.map_comp x.val y.val z.val

lemma objects_homKFlat (hS : S.HomKFlat) : localHomKFlat A S.Objects :=
  fun x y => hS x.val y.val

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation
