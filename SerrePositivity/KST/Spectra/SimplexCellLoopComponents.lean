module

public import SerrePositivity.KST.Spectra.SimplexCellHomotopyGroups
public import SerrePositivity.KST.Spectra.SkeletalFiberComponents

/-!
概要：セル球面の基本群の既存表示と loop 値の成分表示の一致。
方針：loop 写像類の源に関する自然性と標準球面の基本群の定義を使う。
規約：球面の比較同型の向きを変えず、符号変更を加えない。
使われ方：Goerss–Jardine I §7、VIII §1。成分の代表計算と正次数の係数の接続。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SimplexCell

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セル球面の基本群の次数移動は loop 値の成分係数からの次数移動と一致する。
方針：源の同型への自然性で標準球面へ移し、loop 写像類の群同型の順逆を消す。
規約：loop の模型は既存の CirclePower.space。比較の符号は正。
使われ方：Goerss–Jardine I §7。正次数の係数表示の基本段の向きの検査。 -/
theorem positiveHomotopyEquiv_zero_loopClasses (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) (a : LoopMappingClasses (sphere.{u} (n + 1)) Y) :
    positiveHomotopyEquiv Y n 0 (LoopMappingClasses.groupEquiv (sphere.{u} (n + 1)) Y a) =
      CirclePower.positiveHomotopyEquiv Y n
        (componentEquiv (PointedObject.basedHom CirclePower.space.{u} Y) n a) := by
  have h := LoopMappingClasses.classEquiv_pre (sphereIso.{u} (n + 1)).inv Y a
  change SphereSimplex.fundamentalHomotopyEquiv Y n
    (pointedGroupMap
      (X := PointedObject.basedHom (sphere.{u} (n + 1)) Y)
      (Y := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y)
      0 ((MonoidalClosed.pre (sphereIso.{u} (n + 1)).inv).app Y)
      (LoopMappingClasses.classEquiv (sphere.{u} (n + 1)) Y a)) = _
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change SphereSimplex.fundamentalHomotopyEquiv Y n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv Y).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
      (LoopMappingClasses.classEquiv (sphere.{u} (n + 1)) Y a)) = _
  rw [← h]
  change CirclePower.positiveHomotopyEquiv Y n
    (LoopMappingClasses.sphereComponentEquiv Y n
      ((LoopMappingClasses.groupEquiv (PointedSimplicialSet.sphere.{u} (n + 1)) Y).symm
        (LoopMappingClasses.groupEquiv (PointedSimplicialSet.sphere.{u} (n + 1)) Y
          (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv
            (PointedObject.basedHom CirclePower.space Y)).right a)))) = _
  rw [MulEquiv.symm_apply_apply]
  change CirclePower.positiveHomotopyEquiv Y n
    (SphereSimplex.componentClass (PointedObject.basedHom CirclePower.space Y) n
      (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv
        (PointedObject.basedHom CirclePower.space Y)).right a)) = _
  change _ = CirclePower.positiveHomotopyEquiv Y n
    (SphereSimplex.componentClass (PointedObject.basedHom CirclePower.space Y) n
      (mapπ₀ ((MonoidalClosed.pre (sphereIso.{u} (n + 1)).inv).app
        (PointedObject.basedHom CirclePower.space Y)).right a))
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]

end
end SerrePositivity.KST.Spectra.SimplexCell
