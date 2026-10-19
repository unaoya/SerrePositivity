module

public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：単体集合の引き戻しと右 pinched Hom の交換。
方針：全単体パラメータの既存の lift と一意性を極限錐へまとめる。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：引き戻しの右写像空間は両成分の右写像空間の引き戻し。
方針：全単体パラメータの lift・両射影の回収・一意性を使う。
規約：quasicategory 性や fibration 性を仮定しない。
使われ方：lax pullback の対象間写像空間の計算。 -/
def pinchedPullbackCone {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) : PullbackCone
      (pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
        ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))
      (pinchedHomPullbackBaseMap p q v w) :=
  PullbackCone.mk (pinchedHomMap (pullback.fst p q) v w)
    (pinchedHomMap (pullback.snd p q) v w) (pinchedHomPullbackBaseMap_comm p q v w)
/-- 概要：引き戻しの右写像空間は両成分の右写像空間の引き戻し。
方針：全単体パラメータの lift・両射影の回収・一意性を使う。
規約：quasicategory 性や fibration 性を仮定しない。
使われ方：lax pullback の対象間写像空間の計算。 -/
def pinchedPullbackConeLift {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌)
    (s : PullbackCone (pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
        ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))
      (pinchedHomPullbackBaseMap p q v w)) : s.pt ⟶ pinchedHom v w := by
  apply pinchedHomPullbackLift p q v w s.fst s.snd
  intro n a
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app s.condition (Opposite.op ⦋n⦌)) a
  exact congrArg PinchedHom.Simplex.val h
/-- 概要：引き戻しの右写像空間は両成分の右写像空間の引き戻し。
方針：全単体パラメータの lift・両射影の回収・一意性を使う。
規約：quasicategory 性や fibration 性を仮定しない。
使われ方：lax pullback の対象間写像空間の計算。 -/
def pinchedPullbackCone_isLimit {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) : IsLimit (pinchedPullbackCone p q v w) :=
  PullbackCone.IsLimit.mk _ (pinchedPullbackConeLift p q v w)
    (fun s ↦ pinchedHomPullbackLift_fst p q v w s.fst s.snd _)
    (fun s ↦ pinchedHomPullbackLift_snd p q v w s.fst s.snd _)
    (fun s _m hm₁ hm₂ ↦ pinchedHomPullback_hom_ext p q v w
      (hm₁.trans (pinchedHomPullbackLift_fst p q v w s.fst s.snd _).symm)
      (hm₂.trans (pinchedHomPullbackLift_snd p q v w s.fst s.snd _).symm))
/-- 概要：引き戻しの右写像空間は両成分の右写像空間の引き戻し。
方針：全単体パラメータの lift・両射影の回収・一意性を使う。
規約：quasicategory 性や fibration 性を仮定しない。
使われ方：lax pullback の対象間写像空間の計算。 -/
lemma pinchedHom_pullback_isPullback {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    IsPullback (pinchedHomMap (pullback.fst p q) v w)
      (pinchedHomMap (pullback.snd p q) v w)
      (pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
        ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))
      (pinchedHomPullbackBaseMap p q v w) :=
  IsPullback.of_isLimit (pinchedPullbackCone_isLimit p q v w)

end SerrePositivity.InfinityCategories.F2
