module

public import SerrePositivity.InfinityCategories.F2.PinchedHomPullbackLimit
public import SerrePositivity.InfinityCategories.F1.TransportWitnessPushoutContractible
public import SerrePositivity.InfinityCategories.F1B.KanRelativeInitialBoundaryCriterion

/-!
概要：写像空間に Kan fibration を持つ引き戻しの始対象の判定。
方針：三つの成分への写像空間の可縮性を厳密な引き戻しで移す。
規約：元の引き戻し頂点と元の写像空間を使う。
使われ方：lax pullback の成分ごとの始対象と極限錐の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：三成分が始対象である引き戻し頂点は始対象。
方針：各右写像空間を可縮空間の Kan fibration に沿う引き戻しで表示する。
規約：左脚の写像空間の充填性を明示し、余分なモデル構造の仮定を置かない。
使われ方：lax pullback の錐の成分ごとの普遍性。 -/
lemma isInitialVertex_pullback_of_components {E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [Quasicategory (pullback p q)]
    (hp : ∀ x y : E _⦋0⦌, Fibration (pinchedHomMap p x y))
    (x : (pullback p q) _⦋0⦌)
    (he : IsInitialVertex ((pullback.fst p q).app (Opposite.op ⦋0⦌) x))
    (hd : IsInitialVertex ((pullback.snd p q).app (Opposite.op ⦋0⦌) x))
    (hb : IsInitialVertex (p.app (Opposite.op ⦋0⦌)
      ((pullback.fst p q).app (Opposite.op ⦋0⦌) x))) : IsInitialVertex x := by
  apply F1B.kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro y
  have := hp ((pullback.fst p q).app (Opposite.op ⦋0⦌) x)
    ((pullback.fst p q).app (Opposite.op ⦋0⦌) y)
  exact isContractibleKan_of_isPullback_of_fibration
    (pinchedHom_pullback_isPullback p q x y)
    (F1B.kanInitialVertex_pinchedHom_isContractibleKan he _)
    (F1B.kanInitialVertex_pinchedHom_isContractibleKan hd _)
    (F1B.kanInitialVertex_pinchedHom_isContractibleKan hb _)

end SerrePositivity.InfinityCategories.F2
