module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIntervalLaws
public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalOrderTransport
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFactorOrder

/-!
概要：同じ全単体の二つの水平分解の間の残りの実関手を構成する。
方針：各頂点の残りの対象と、その間への実区間制限を端点条件つきで回収する。
規約：実関手やその法則の存在を仮定しない。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：左因子の全頂点の長さの比較を、同じH上の切れ目の順位へ移す。
方針：既存の順位と長さの照合を使う。規約：始点の補正は共通。
使われ方：Riehl–Verity Proposition 3.1.10 の実残余因子。 -/
lemma WalkingAdjunctionFactorization.rank_le_of_prefix_le (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    ∀ i, walkingAdjunctionCutRank a.cut i ≤ walkingAdjunctionCutRank b.cut i := by
  intro i
  rw [a.cut_rank i, b.cut_rank i]
  exact Nat.add_le_add_right (h i) _

/-- 概要：分解の切れ目の座標は左因子の重み。
方針：順位の比較から中点の補正を相殺する。規約：同じH上の切れ目。
使われ方：Riehl–Verity Proposition 3.1.10 の残りの個数の照合。 -/
lemma WalkingAdjunctionFactorization.cut_coordinate (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate a.cut i = walkingAdjunctionWeight X a.middle (a.left.obj i) := by
  have hc := a.cut_rank i
  have hw := walkingAdjunctionVertexLength_weight X a.middle (a.left.obj i)
  unfold walkingAdjunctionCutRank at hc
  omega

/-- 概要：残りの実対象の点の個数は切れ目の間の区間の個数と一致する。
方針：重みの差と二つの切れ目の座標を照合する。
規約：実対象の個数の等式。使われ方：Riehl–Verity Proposition 3.1.10 の型の移送。 -/
lemma WalkingAdjunctionFactorization.residualObject_card (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard a.middle b.middle
      (walkingAdjunctionResidualObject (a.left.obj i) (b.left.obj i) (h i)) =
        walkingAdjunctionCutIntervalSize a.cut b.cut i := by
  rw [walkingAdjunctionOrdinalCard_weight, walkingAdjunctionResidualObject_weight]
  simp only [walkingAdjunctionCutIntervalSize, a.cut_coordinate, b.cut_coordinate]

/-- 概要：残りの実対象の間の射。
方針：実区間制限を個数の等式で移し、四Homの全単射で戻す。
規約：端点条件も構成済みの証明から与える。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def WalkingAdjunctionFactorization.residualMap (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionResidualObject (a.left.obj i) (b.left.obj i) (h i) ⟶
      walkingAdjunctionResidualObject (a.left.obj j) (b.left.obj j) (h j) :=
  walkingAdjunctionHomOfOrder _ _
    (ordinalOrderHomTransport (a.residualObject_card b h i).symm (a.residualObject_card b h j).symm
      (walkingAdjunctionCutIntervalMap a.cut b.cut (a.rank_le_of_prefix_le b h) (leOfHom f)))
    (ordinalOrderHomTransport_boundary _ _ a.middle b.middle _
      (walkingAdjunctionCutIntervalMap_boundary a.cut b.cut
        (a.rank_le_of_prefix_le b h) (leOfHom f)))

/-- 概要：残りの実射の共通表示は構成した区間制限の輸送と同じ。
方針：実射の回収と表示の往復を使う。規約：全ての射を含む。
使われ方：Riehl–Verity Proposition 3.1.10 の実関手の法則の回収。 -/
lemma WalkingAdjunctionFactorization.residualMap_profile (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionOrderHom (a.residualMap b h f) =
      ordinalOrderHomTransport (a.residualObject_card b h i).symm (a.residualObject_card b h j).symm
        (walkingAdjunctionCutIntervalMap a.cut b.cut (a.rank_le_of_prefix_le b h) (leOfHom f)) :=
  walkingAdjunctionOrderHom_ofOrder _ _ _ _

/-- 概要：二つの水平分解の間の残りの実関手。
方針：残りの実対象と実射を組み立て、端点・恒等射・全合成の証明を忠実な表示から戻す。
規約：関手やその法則の存在は引数に置かない。
使われ方：Riehl–Verity Proposition 3.1.10 の原子的な分解の一意性の構成。 -/
def WalkingAdjunctionFactorization.residualFunctor (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle where
  obj i := walkingAdjunctionResidualObject (a.left.obj i) (b.left.obj i) (h i)
  map f := a.residualMap b h f
  map_id i := by
    apply walkingAdjunctionOrderHom_injective
    rw [a.residualMap_profile, walkingAdjunctionOrderHom_id, walkingAdjunctionCutIntervalMap_id]
    exact ordinalOrderHomTransport_id _
  map_comp {i j k} f g := by
    apply walkingAdjunctionOrderHom_injective
    rw [a.residualMap_profile, walkingAdjunctionOrderHom_comp,
      a.residualMap_profile, a.residualMap_profile]
    rw [walkingAdjunctionCutIntervalMap_comp a.cut b.cut (a.rank_le_of_prefix_le b h)
      (leOfHom f) (leOfHom g), ordinalOrderHomTransport_comp]

end SerrePositivity.InfinityCategories.HA.Monads
