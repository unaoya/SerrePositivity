module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftPrismCutMinimumCoordinates

/-!
概要：native な左切断の path の作用と、weighted cone の切断後の係数射を同定する。
方針：正頂点への移送と零時刻の崩壊を path の包含圏の関手として明示する。
規約：path の点集合の像を保ち、座標の点ごとの一致を単体集合の射の等式にする。
使われ方：左 Hom 区間の正頂点間の Hom と weighted prism の係数の接続。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations


/-- 元の path の全ての点を、cone の正頂点へ移す。 -/
def pathPositiveShift {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) where
  I := (fun k : ULift.{u} (Fin (n + 1)) => ULift.up k.down.succ) '' P.I
  left := ⟨ULift.up i, P.left, rfl⟩
  right := ⟨ULift.up j, P.right, rfl⟩
  left_le k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact Fin.succ_le_succ_iff.mpr (P.left_le l hl)
  le_right k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact Fin.succ_le_succ_iff.mpr (P.le_right l hl)

/-- 正頂点への移送は path の包含に自然。 -/
def pathPositiveShiftFunctor {n : ℕ} (i j : Fin (n + 1)) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤
      Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) where
  obj := pathPositiveShift
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 混合 Hom の path を、元の左区間の切断写像で初点からの path にする。 -/
def leftPrismCutPath {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) where
  I := (fun k : ULift.{u} (Fin (n + 1)) => ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t k.down)) '' P.I
  left := ⟨ULift.up i, P.left, congrArg ULift.up (ite_eq_left hi)⟩
  right := ⟨ULift.up j, P.right, congrArg ULift.up (ite_eq_right (by rw [hj]; decide))⟩
  left_le k _ := Fin.zero_le k.down
  le_right k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t).monotone (P.le_right l hl)
    have hj' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t j = j.succ := ite_eq_right (by rw [hj]; decide)
    exact h.trans_eq hj'

/-- 左切断による path の像は包含圏の関手。 -/
def leftPrismCutPathFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤
      Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) where
  obj := leftPrismCutPath t hi hj
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 同じ正頂点間の全 Hom で、元の左切断の座標と weighted 切断座標は厳密に一致。 -/
lemma pathCutMinimumMap_eq_leftPrismCut {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    nerveMap (pathPositiveShiftFunctor i j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj =
      nerveMap (leftPrismCutPathFunctor t i j hi hj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫
        SSet.opFunctor.map (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (by omega))) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro k
  change (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d
    (P ⋙ pathPositiveShiftFunctor i j))).down.toOrderHom k =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (by omega)).toOrderHom
      ((SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j).app d
        (P ⋙ leftPrismCutPathFunctor t i j hi hj))).down.toOrderHom k)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap_apply]
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj (pathPositiveShift (P.obj k.rev))).val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum (leftPrismCutPath t hi hj (P.obj k.rev))).val
  exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathCutMinimum_eq_pathFirstMinimum t hj (P.obj k.rev)
    (pathPositiveShift (P.obj k.rev)) (leftPrismCutPath t hi hj (P.obj k.rev)) rfl rfl)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
