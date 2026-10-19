module

public import SerrePositivity.InfinityCategories.F1B.KanPinchedHomPullbackLift

/-!
概要：引き戻し四角形は指定された端点間の pinched 写像空間でも引き戻しになる。
方針：底の端点の表示を等式で揃え、展開した族の持ち上げと一意性を使う。
規約：全ての単体集合に充填性は不要。
使われ方：相対内部 Hom の写像空間を四つの関手圏の写像空間から計算する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：可換正方形の右下の pinched 作用の端点を左下の表示に揃える。
方針：底への二つの像の等式で右の作用の端点を輸送する。
規約：輸送は単体の値を保つ。
使われ方：写像空間の四角形を同じ底の対象上に書く。 -/
def kanPinchedPullbackRightMap {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : CommSq a b p q) (v w : P _⦋0⦌) :
    pinchedHom (b.app (Opposite.op ⦋0⦌) v) (b.app (Opposite.op ⦋0⦌) w) ⟶
      pinchedHom (p.app (Opposite.op ⦋0⦌) (a.app (Opposite.op ⦋0⦌) v))
        (p.app (Opposite.op ⦋0⦌) (a.app (Opposite.op ⦋0⦌) w)) :=
  pinchedHomMap q _ _ ≫ (kanPinchedHomTransportIso
    (ConcreteCategory.congr_hom (NatTrans.congr_app h.w (Opposite.op ⦋0⦌)) v).symm
    (ConcreteCategory.congr_hom (NatTrans.congr_app h.w (Opposite.op ⦋0⦌)) w).symm).hom

/-- 概要：端点を揃えた pinched 作用の四角形は可換。
方針：各単体の値で元の正方形の可換性を読む。
規約：相対的な端点は指定された二頂点の像。
使われ方：引き戻し錐を定義する可換性。 -/
lemma kanPinchedHom_square {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : CommSq a b p q) (v w : P _⦋0⦌) :
    pinchedHomMap a v w ≫ pinchedHomMap p _ _ =
      pinchedHomMap b v w ≫ kanPinchedPullbackRightMap h v w := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply PinchedHom.Simplex.ext
  simp only [kanPinchedPullbackRightMap, NatTrans.comp_app_apply]
  have ht := kanPinchedHomTransportIso_hom_val
    (ConcreteCategory.congr_hom (NatTrans.congr_app h.w (Opposite.op ⦋0⦌)) v).symm
    (ConcreteCategory.congr_hom (NatTrans.congr_app h.w (Opposite.op ⦋0⦌)) w).symm n
    ((pinchedHomMap q _ _).app (Opposite.op ⦋n⦌)
      ((pinchedHomMap b v w).app (Opposite.op ⦋n⦌) s))
  have hr : p.app (Opposite.op ⦋n + 1⦌) (a.app (Opposite.op ⦋n + 1⦌) s.val) =
      q.app (Opposite.op ⦋n + 1⦌) (b.app (Opposite.op ⦋n + 1⦌) s.val) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app h.w (Opposite.op ⦋n + 1⦌)) s.val
  exact hr.trans ht.symm

/-- 概要：任意の引き戻しは端点を固定した pinched 写像空間の引き戻しを誘導する。
方針：一致する族を join 上で持ち上げ、両射影と一意性を使う。
規約：標準の引き戻しの選択によらない。
使われ方：相対制限の比較を四つの写像空間の比較へ移す。 -/
lemma kanPinchedHom_isPullback {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : IsPullback a b p q) (v w : P _⦋0⦌) :
    IsPullback (pinchedHomMap a v w) (pinchedHomMap b v w)
      (pinchedHomMap p _ _) (kanPinchedPullbackRightMap h.toCommSq v w) := by
  let lift (c : PullbackCone (pinchedHomMap p
      (a.app (Opposite.op ⦋0⦌) v) (a.app (Opposite.op ⦋0⦌) w))
        (kanPinchedPullbackRightMap h.toCommSq v w)) : c.pt ⟶ pinchedHom v w :=
    kanPinchedHomPullbackLift h v w c.fst c.snd (by
      have hc := congrArg pinchedHomUncurry c.condition
      dsimp only [kanPinchedPullbackRightMap] at hc
      rw [← Category.assoc, kanPinchedHomTransportIso_uncurry,
        pinchedHomUncurry_postcomp, pinchedHomUncurry_postcomp] at hc
      exact hc)
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk (kanPinchedHom_square h.toCommSq v w)
    lift ?_ ?_ ?_)
  · intro c
    exact kanPinchedHomPullbackLift_fst h v w c.fst c.snd _
  · intro c
    exact kanPinchedHomPullbackLift_snd h v w c.fst c.snd _
  · intro c m hm₁ hm₂
    apply kanPinchedHomPullback_hom_ext h v w
    · exact hm₁.trans (kanPinchedHomPullbackLift_fst h v w c.fst c.snd _).symm
    · exact hm₂.trans (kanPinchedHomPullbackLift_snd h v w c.fst c.snd _).symm

end SerrePositivity.InfinityCategories.F1B
