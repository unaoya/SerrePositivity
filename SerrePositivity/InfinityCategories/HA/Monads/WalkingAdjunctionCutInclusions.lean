module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutFunctor
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixInclusions

/-!
概要：任意の比較された切れ目の間の実関手を、元の全単体の区間へ入れる。
方針：個数の等式を通して既存の実区間包含と可換正方形を移す。
規約：切れ目が実分解から来るという仮定は使わない。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の区間の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：実区間関手の各対象を元のHへ入れる実包含。
方針：個数の等式で移して既存の区間包含を使う。規約：値を変えない輸送。
使われ方：Riehl–Verity §4.1の実区間の比較。 -/
def walkingAdjunctionCutFunctorInclusion
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard M N ((walkingAdjunctionCutIntervalFunctor a b h).obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i)) :=
  (walkingAdjunctionCutIntervalInclusion a b h i).comp
    (Fin.castOrderIso (walkingAdjunctionCutIntervalObject_card a b h i)).toOrderEmbedding.toOrderHom

/-- 概要：区間包含の値は左端の座標を加えた値。
方針：個数の輸送は値を保持する。規約：全点。
使われ方：Riehl–Verity §4.1の全射の照合。 -/
lemma walkingAdjunctionCutFunctorInclusion_val
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1))
    (x : Fin (walkingAdjunctionOrdinalCard M N
      ((walkingAdjunctionCutIntervalFunctor a b h).obj i))) :
    (walkingAdjunctionCutFunctorInclusion a b h i x).val =
      walkingAdjunctionCutCoordinate a i + x.val := rfl

/-- 概要：実区間射の共通表示は元の区間制限と異種等式で一致する。
方針：実射の回収と個数の輸送をつなぐ。規約：全射。
使われ方：Riehl–Verity §4.1の可換正方形。 -/
lemma walkingAdjunctionCutIntervalHom_heq
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    HEq (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f))
      (walkingAdjunctionCutIntervalMap a b h (leOfHom f)) :=
  (heq_of_eq (walkingAdjunctionCutIntervalHom_profile a b h f)).trans
    (ordinalOrderHomTransport_heq _ _ _)

/-- 概要：実区間関手の全射は元のHへの実包含と可換。
方針：個数の輸送の値の照合と区間制限の正方形をつなぐ。
規約：全ての射の正方形。使われ方：Riehl–Verity §4.1の全関手の照合。 -/
lemma walkingAdjunctionCutFunctor_square
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (walkingAdjunctionCutFunctorInclusion a b h j).comp
        (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp
        (walkingAdjunctionCutFunctorInclusion a b h i) := by
  apply OrderHom.ext
  funext x
  apply Fin.ext
  let x' := (Fin.castOrderIso (walkingAdjunctionCutIntervalObject_card a b h i)) x
  have hm := ordinalOrderHom_heq_val (walkingAdjunctionCutIntervalObject_card a b h i)
    (walkingAdjunctionCutIntervalObject_card a b h j) _ _
    (walkingAdjunctionCutIntervalHom_heq a b h f) x x' rfl
  have hs := walkingAdjunctionCutInterval_square_apply a b h (leOfHom f) x'
  change walkingAdjunctionCutCoordinate a j +
      (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f) x).val =
    (walkingAdjunctionOrderHom (H.map f) (walkingAdjunctionCutFunctorInclusion a b h i x)).val
  exact (congrArg (fun v : ℕ => walkingAdjunctionCutCoordinate a j + v) hm).trans
    (congrArg Fin.val hs)

end SerrePositivity.InfinityCategories.HA.Monads
