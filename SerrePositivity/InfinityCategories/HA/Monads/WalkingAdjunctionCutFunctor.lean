module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIntervalLaws
public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalOrderTransport
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionResidualObjects

/-!
概要：比較された任意の二つの切れ目の間に元の四Homの実関手を作る。
方針：座標差の対象と、区間制限の射を端点条件つきで回収する。
規約：切れ目が既存の分解から来るという仮定を置かない。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：比較された切れ目の座標差は混合Homの非空条件を満たす。
方針：順位の偶奇の補正を比較する。規約：minusからplusへの場合に正。
使われ方：Riehl–Verity §4.1の実区間の対象の回収。 -/
lemma walkingAdjunctionCut_difference_admissible
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) : M = .minus → N = .plus →
      0 < walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i := by
  intro hM hN
  subst M
  subst N
  have hi := h i
  simp only [walkingAdjunctionCutRank, walkingAdjunctionTargetCorrection] at hi
  omega

/-- 概要：二つの切れ目の間の実Homの対象。
方針：座標差を重みとして元の対象を作る。規約：非空条件は順位から証明する。
使われ方：Riehl–Verity §4.1の区間の実関手。 -/
def walkingAdjunctionCutIntervalObject
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) : walkingAdjunctionHom M N :=
  walkingAdjunctionObjectOfWeight M N
    (walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i)
    (walkingAdjunctionCut_difference_admissible a b h i)

/-- 概要：区間の実対象の重みは切れ目の座標差。
方針：重みからの対象の回収則を使う。規約：四Hom全てを含む。
使われ方：Riehl–Verity §4.1の実対象の照合。 -/
lemma walkingAdjunctionCutIntervalObject_weight
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) :
    walkingAdjunctionWeight M N (walkingAdjunctionCutIntervalObject a b h i) =
      walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i :=
  walkingAdjunctionObjectOfWeight_weight _ _ _ _

/-- 概要：区間の実対象の個数は既存の区間制限の個数と一致する。
方針：重みと終点の補正を照合する。規約：自然数の等式。
使われ方：Riehl–Verity §4.1の射の型の移送。 -/
lemma walkingAdjunctionCutIntervalObject_card
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard M N (walkingAdjunctionCutIntervalObject a b h i) =
      walkingAdjunctionCutIntervalSize a b i := by
  rw [walkingAdjunctionOrdinalCard_weight, walkingAdjunctionCutIntervalObject_weight]
  rfl

/-- 概要：区間の実対象の間の射。
方針：区間制限を個数の等式で移して元のHomの射へ戻す。
規約：端点条件は構成済みの区間制限から与える。使われ方：Riehl–Verity §4.1。 -/
def walkingAdjunctionCutIntervalHom
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionCutIntervalObject a b h i ⟶ walkingAdjunctionCutIntervalObject a b h j :=
  walkingAdjunctionHomOfOrder _ _
    (ordinalOrderHomTransport (walkingAdjunctionCutIntervalObject_card a b h i).symm
      (walkingAdjunctionCutIntervalObject_card a b h j).symm
      (walkingAdjunctionCutIntervalMap a b h (leOfHom f)))
    (ordinalOrderHomTransport_boundary _ _ M N _
      (walkingAdjunctionCutIntervalMap_boundary a b h (leOfHom f)))

/-- 概要：実射の共通表示は区間制限の輸送に一致する。
方針：射の表示と回収の往復を使う。規約：任意の射を含む。
使われ方：Riehl–Verity §4.1の単位則と全合成則。 -/
lemma walkingAdjunctionCutIntervalHom_profile
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionOrderHom (walkingAdjunctionCutIntervalHom a b h f) =
      ordinalOrderHomTransport (walkingAdjunctionCutIntervalObject_card a b h i).symm
        (walkingAdjunctionCutIntervalObject_card a b h j).symm
        (walkingAdjunctionCutIntervalMap a b h (leOfHom f)) :=
  walkingAdjunctionOrderHom_ofOrder _ _ _ _

/-- 概要：比較された任意の二つの切れ目の間の実関手。
方針：区間の実対象と実射を組み、忠実な共通表示から関手則を戻す。
規約：分解や関手の存在を引数に置かない。使われ方：Riehl–Verity §4.1–§4.2。 -/
def walkingAdjunctionCutIntervalFunctor
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) :
    Fin (n + 1) ⥤ walkingAdjunctionHom M N where
  obj i := walkingAdjunctionCutIntervalObject a b h i
  map f := walkingAdjunctionCutIntervalHom a b h f
  map_id i := by
    apply walkingAdjunctionOrderHom_injective
    rw [walkingAdjunctionCutIntervalHom_profile, walkingAdjunctionOrderHom_id,
      walkingAdjunctionCutIntervalMap_id]
    exact ordinalOrderHomTransport_id _
  map_comp {i j k} f g := by
    apply walkingAdjunctionOrderHom_injective
    rw [walkingAdjunctionCutIntervalHom_profile, walkingAdjunctionOrderHom_comp,
      walkingAdjunctionCutIntervalHom_profile, walkingAdjunctionCutIntervalHom_profile]
    rw [walkingAdjunctionCutIntervalMap_comp a b h (leOfHom f) (leOfHom g),
      ordinalOrderHomTransport_comp]

end SerrePositivity.InfinityCategories.HA.Monads
