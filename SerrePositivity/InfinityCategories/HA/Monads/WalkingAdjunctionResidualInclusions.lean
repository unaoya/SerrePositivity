module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixInclusions

/-!
概要：残りの実関手を元の全単体の区間へ入れ、その全射の可換性を証明する。
方針：個数の等式による輸送を区間への実包含へつなぐ。
規約：元のHと実残余関手の射を保持する。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの因子の合成の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：左因子の個数は切れ目の座標と中点の補正の和。
方針：重みと共通表示の個数を照合する。
規約：同じH上の切れ目。使われ方：Riehl–Verity Proposition 3.1.10 の先頭と残りの境界。 -/
lemma WalkingAdjunctionFactorization.prefix_card (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard X a.middle (a.left.obj i) =
      walkingAdjunctionCutCoordinate a.cut i + walkingAdjunctionTargetCorrection a.middle := by
  simp only [walkingAdjunctionOrdinalCard_weight, a.cut_coordinate]

/-- 概要：残りの実関手の各対象を元のHの区間へ入れる実包含。
方針：同じ個数へ移して構成済みの区間の包含を使う。
規約：値を変えない個数の輸送を使う。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def WalkingAdjunctionFactorization.residualInclusion (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard a.middle b.middle ((a.residualFunctor b h).obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i)) :=
  (walkingAdjunctionCutIntervalInclusion a.cut b.cut (a.rank_le_of_prefix_le b h) i).comp
    (Fin.castOrderIso (a.residualObject_card b h i)).toOrderEmbedding.toOrderHom

/-- 概要：残りの区間への実包含の値は始点の座標を加えた値。
方針：個数の輸送が値を変えないことを使う。
規約：実対象の全点。使われ方：Riehl–Verity Proposition 3.1.10 の全射の照合。 -/
lemma WalkingAdjunctionFactorization.residualInclusion_val (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) (i : Fin (n + 1))
    (x : Fin (walkingAdjunctionOrdinalCard a.middle b.middle
      ((a.residualFunctor b h).obj i))) :
    (a.residualInclusion b h i x).val = walkingAdjunctionCutCoordinate a.cut i + x.val := rfl

/-- 概要：残りの実射の共通表示は、元の区間制限と異種等式で一致する。
方針：実射の回収の往復と、個数の輸送の異種等式を合わせる。
規約：全ての射を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.residualMap_interval_heq
    (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    HEq (walkingAdjunctionOrderHom ((a.residualFunctor b h).map f))
      (walkingAdjunctionCutIntervalMap a.cut b.cut (a.rank_le_of_prefix_le b h) (leOfHom f)) :=
  (heq_of_eq (a.residualMap_profile b h f)).trans (ordinalOrderHomTransport_heq _ _ _)

/-- 概要：残りの実関手の全射は元のHへの区間包含と可換。
方針：共通表示の実回収と、切れ目の間の正方形を同じ点で比較する。
規約：全射の正方形として検収する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.residual_square (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (a.residualInclusion b h j).comp (walkingAdjunctionOrderHom ((a.residualFunctor b h).map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp (a.residualInclusion b h i) := by
  apply OrderHom.ext
  funext x
  apply Fin.ext
  let x' := (Fin.castOrderIso (a.residualObject_card b h i)) x
  have hm := ordinalOrderHom_heq_val (a.residualObject_card b h i)
    (a.residualObject_card b h j) _ _ (a.residualMap_interval_heq b h f) x x' rfl
  have hs := walkingAdjunctionCutInterval_square_apply a.cut b.cut
    (a.rank_le_of_prefix_le b h) (leOfHom f) x'
  change walkingAdjunctionCutCoordinate a.cut j +
      (walkingAdjunctionOrderHom ((a.residualFunctor b h).map f) x).val =
    (walkingAdjunctionOrderHom (H.map f) (a.residualInclusion b h i x)).val
  exact (congrArg (fun v : ℕ => walkingAdjunctionCutCoordinate a.cut j + v) hm).trans
    (congrArg Fin.val hs)

end SerrePositivity.InfinityCategories.HA.Monads
