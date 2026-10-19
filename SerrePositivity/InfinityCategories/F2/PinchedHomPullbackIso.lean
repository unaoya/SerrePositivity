module

public import SerrePositivity.InfinityCategories.F2.PinchedHomPullbackLimit

/-!
概要：右写像空間の引き戻し表示の標準同型と両射影。
方針：極限錐から引き戻しへの比較同型を取る。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：右写像空間の引き戻し表示の標準同型と両射影。
方針：極限錐から引き戻しへの比較同型を取る。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
def pinchedHomPullbackIso {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    pinchedHom v w ≅ pullback
      (pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
        ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))
      (pinchedHomPullbackBaseMap p q v w) :=
  (pinchedHom_pullback_isPullback p q v w).isoPullback
/-- 概要：右写像空間の引き戻し表示の標準同型と両射影。
方針：極限錐から引き戻しへの比較同型を取る。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
lemma pinchedHomPullbackIso_fst {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    (pinchedHomPullbackIso p q v w).hom ≫ pullback.fst _ _ =
      pinchedHomMap (pullback.fst p q) v w :=
  (pinchedHom_pullback_isPullback p q v w).isoPullback_hom_fst
/-- 概要：右写像空間の引き戻し表示の標準同型と両射影。
方針：極限錐から引き戻しへの比較同型を取る。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
lemma pinchedHomPullbackIso_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    (pinchedHomPullbackIso p q v w).hom ≫ pullback.snd _ _ =
      pinchedHomMap (pullback.snd p q) v w :=
  (pinchedHom_pullback_isPullback p q v w).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.F2
