module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestrictionValue
public import SerrePositivity.DifferentialGraded.Complexes.MapComponentFunctions

/-! # 外側右制限比較の値を固定した成分関数で表示する

## 概要
外側右制限比較の値を固定した成分関数で表示する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 右制限比較の構成を展開せずに使う、型を固定した次数別成分関数。 -/
@[irreducible]
def composeRightRestrictionValueComponent (d : D) (e : E) (n : ℤ) :
    ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).value d e).X n →
      ((compose A B C E P Q).value (F.obj d) e).X n :=
  fun x => (composeRightRestrictionValueIso A B D C E F P Q d e).hom.f n x

lemma composeRightRestrictionValueComponent_eq (d : D) (e : E) (n : ℤ) (x) :
    composeRightRestrictionValueComponent A B D C E F P Q d e n x =
      (composeRightRestrictionValueIso A B D C E F P Q d e).hom.f n x := by
  unfold composeRightRestrictionValueComponent
  rfl

/-- 固定成分による再表示は、元の右制限比較と同じchain mapである。 -/
def composeRightRestrictionValueHom (d : D) (e : E) :
    (compose A D C E (Bimodule.rightRestriction A B D C F P) Q).value d e ⟶
      (compose A B C E P Q).value (F.obj d) e :=
  chainMapOfComponentFunctions (composeRightRestrictionValueIso A B D C E F P Q d e).hom
    (composeRightRestrictionValueComponent A B D C E F P Q d e)
    (composeRightRestrictionValueComponent_eq A B D C E F P Q d e)

@[simp]
lemma composeRightRestrictionValueHom_apply (d : D) (e : E) (n : ℤ) (x) :
    (composeRightRestrictionValueHom A B D C E F P Q d e).f n x =
      composeRightRestrictionValueComponent A B D C E F P Q d e n x := rfl

lemma composeRightRestrictionValueHom_eq (d : D) (e : E) :
    composeRightRestrictionValueHom A B D C E F P Q d e =
      (composeRightRestrictionValueIso A B D C E F P Q d e).hom :=
  chainMapOfComponentFunctions_eq _ _ _

lemma composeRightRestrictionValueComponent_element (d : D) (c : C) (e : E)
    {r s n : ℤ} (hn : r + s = n) (q : (Q.value c e).X r)
    (p : (P.value (F.obj d) c).X s) :
    composeRightRestrictionValueComponent A B D C E F P Q d e n
        (BalancedTensor.element A C (Q.rightAt e)
          ((Bimodule.rightRestriction A B D C F P).leftAt d) c q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt (F.obj d)) c q p hn :=
  (composeRightRestrictionValueComponent_eq A B D C E F P Q d e n _).trans
    (composeRightRestrictionValueIso_element A B D C E F P Q d c e hn q p)

end SerrePositivity.DifferentialGraded.BimoduleTensor
