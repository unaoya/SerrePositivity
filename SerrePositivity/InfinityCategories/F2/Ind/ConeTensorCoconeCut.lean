module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCornerImage

/-!
概要：補間余錐の外側の切断を比較後の二座標から回収する。
方針：二つの座標の切断の最大値が外側の切断になることを示す。
規約：任意の元の両形状と全境界を保持し、有限性を要求しない。
使われ方：有限半順序形状の点追加における相対補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：補間余錐の外側の切断を比較後の二座標から回収する。
方針：二つの座標の切断の最大値が外側の切断になることを示す。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
noncomputable def coneTensorAugX (A L : SSet.{u}) (r : ℕ)
    (q : Join.augObj (coneTensorCorner A L) r) : StableAugJoin A Δ[0] r :=
  stableAugJoinEquiv A Δ[0] r
    (Join.augHom (coneTensorCornerInclusion A L ≫ fst _ _) r q)
/-- 概要：補間余錐の外側の切断を比較後の二座標から回収する。
方針：二つの座標の切断の最大値が外側の切断になることを示す。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
noncomputable def coneTensorAugY (A L : SSet.{u}) (r : ℕ)
    (q : Join.augObj (coneTensorCorner A L) r) : StableAugJoin L Δ[0] r :=
  stableAugJoinEquiv L Δ[0] r
    (Join.augHom (coneTensorCornerInclusion A L ≫ snd _ _) r q)
/-- 概要：補間余錐の外側の切断を比較後の二座標から回収する。
方針：二つの座標の切断の最大値が外側の切断になることを示す。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorAug_max_cut (A L : SSet.{u}) (r : ℕ)
    (q : Join.augObj (coneTensorCorner A L) r) :
    max (coneTensorAugX A L r q).1.val (coneTensorAugY A L r q).1.val = r := by
  cases r with
  | zero => rfl
  | succ r => exact coneTensorCornerInclusion_max_cut q
/-- 概要：補間余錐の外側の切断を比較後の二座標から回収する。
方針：二つの座標の切断の最大値が外側の切断になることを示す。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorCocone_cut_max {A L : SSet.{u}} {n : ℕ}
    (s : Join.Simplex (coneTensorCorner A L) Δ[0] n) :
    max (((coneTensorCocone A L).app (Opposite.op ⦋n⦌) s).1.1.val)
      (((coneTensorCocone A L).app (Opposite.op ⦋n⦌) s).2.1.val) = s.1.val := by
  have hx : ((coneTensorCocone A L).app (Opposite.op ⦋n⦌) s).1.1.val =
      (coneTensorAugX A L s.1.val s.2.1).1.val :=
    arrowInterpolationConeFold_cut _
  have hy : ((coneTensorCocone A L).app (Opposite.op ⦋n⦌) s).2.1.val =
      (coneTensorAugY A L s.1.val s.2.1).1.val :=
    arrowInterpolationConeFold_cut _
  rw [hx, hy]
  exact coneTensorAug_max_cut A L _ _


end SerrePositivity.InfinityCategories.F2.Ind
