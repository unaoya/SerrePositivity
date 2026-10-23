module

public import SerrePositivity.InfinityCategories.F1.Coherent.PathCutMinimumReindex
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedCoherentCoefficients

/-!
概要：時間切断後の最小点の係数射は、cone の二種類の合成を厳密に保つ。
方針：全次数の各頂点で最小点の合成則と端点での正規化を使う。
規約：正頂点からの path にも同じ座標射を用いる。
使われ方：weighted prism の始点固定 Hom の豊穣合成則と時刻一の終点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 中間点が時刻零のとき、切断後の座標は後半の Hom を通る。 -/
lemma pathCutMinimumMap_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (a : Fin (n + 2)) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    eComp SSet (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ pathCutMinimumMap t hj =
      snd _ _ ≫ pathCutMinimumMap t hj := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro k
  change (SSet.opObjEquiv ((pathCutMinimumMap t hj).app d
    ((eComp SSet (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)))).down.toOrderHom k =
    (SSet.opObjEquiv ((pathCutMinimumMap t hj).app d Q)).down.toOrderHom k
  rw [pathCutMinimumMap_apply, pathCutMinimumMap_apply]
  exact pathCutMinimum_comp_zero t hi hj (P.obj k.rev) (Q.obj k.rev)

/-- 中間点が時刻一のとき、切断後の座標は前半の Hom を通る。 -/
lemma pathCutMinimumMap_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (a : Fin (n + 2)) (i j : Fin (n + 1)) (hi : t i = 1) (hj : t j = 1) :
    eComp SSet (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ pathCutMinimumMap t hj =
      fst _ _ ≫ pathCutMinimumMap t hi := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro k
  change (SSet.opObjEquiv ((pathCutMinimumMap t hj).app d
    ((eComp SSet (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)))).down.toOrderHom k =
    (SSet.opObjEquiv ((pathCutMinimumMap t hi).app d P)).down.toOrderHom k
  rw [pathCutMinimumMap_apply, pathCutMinimumMap_apply]
  exact pathCutMinimum_comp_one t hi hj (P.obj k.rev) (Q.obj k.rev)

/-- 時刻一の終点では、同じ座標射が元の weighted cone の初区間座標を回収する。 -/
lemma pathCutMinimumMap_eq_firstMinimum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (ht : ∀ k, t k = 1) (j : Fin (n + 1)) :
    pathCutMinimumMap (a := 0) t (ht j) = pathFirstMinimumMap j ≫
      SSet.opFunctor.map (stdSimplex.map (simplexPrefixInclusion j.val n (by omega))) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro k
  change (SSet.opObjEquiv ((pathCutMinimumMap t (ht j)).app d P)).down.toOrderHom k =
    (simplexPrefixInclusion j.val n (by omega)).toOrderHom
      ((SSet.opObjEquiv ((pathFirstMinimumMap j).app d P)).down.toOrderHom k)
  rw [pathCutMinimumMap_apply, pathFirstMinimumMap_apply]
  apply Fin.ext
  change (pathCutMinimum t (ht j) (P.obj k.rev)).val = (pathFirstMinimum (P.obj k.rev)).val
  rw [pathCutMinimum_eq_firstMinimum t ht]

end SerrePositivity.InfinityCategories
