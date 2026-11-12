module

public import SerrePositivity.KST.Spectra.SkeletalFiberLoopPositive

/-!
概要：骨格 fiber の全正次数係数を反復 loop 値の fiber の連結成分で表示する。
方針：基本群の成分比較から出発し、正次数の loop 比較を帰納的に合成する。
規約：既存の係数群同型と符号をすべての次数で保持する。
使われ方：Goerss–Jardine I §7、VIII §1。成分での障害計算を全高次群へ運ぶ。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の loop を指定回数だけ反復する。
方針：係数を一回 loop にして残りの反復を行う。
規約：Kan 置換した円は最後の成分比較だけで使用する。
使われ方：Goerss–Jardine I §7。高次数を成分へ下げる係数。 -/
def iteratedLoopSpace : ℕ → PointedSimplicialSet.{u} → PointedSimplicialSet.{u}
  | 0, Y => Y
  | r + 1, Y => iteratedLoopSpace r (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)

instance iteratedLoopSpace_kanComplex (r : ℕ) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] : KanComplex (iteratedLoopSpace r Y).right := by
  induction r generalizing Y with
  | zero => exact inferInstanceAs (KanComplex Y.right)
  | succ r ih => exact ih (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)

/-- 概要：反復 loop の正次数群を元の係数の高次群へ戻す。
方針：通常の loop の群同型を反復回数について合成する。
規約：始域の実際の次数は q+1、終域は q+r+1。
使われ方：Goerss–Jardine I §7。反復した係数の次数の管理。 -/
def iteratedLoopGroupEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (q : ℕ) :
    (r : ℕ) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (iteratedLoopSpace r Y).right q
        (iteratedLoopSpace r Y).basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (q + r) Y.basepoint
  | 0 => MulEquiv.refl _
  | r + 1 => (iteratedLoopGroupEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) q r).trans
      (loopPositiveHomotopyEquiv Y (q + r))

namespace SkeletalCellAttachment

/-- 概要：反復 loop 値の fiber の連結成分と元の fiber の全正次数群の同値。
方針：基本群の成分比較に、一段ずつの正次数群の loop 比較を合成する。
規約：r は元の fiber の実際の次数 r+1 より一つ小さい。
使われ方：Goerss–Jardine VIII §1。全高次数の幾何的代表の供給。 -/
def stageFiberIteratedLoopComponentEquiv (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    (r : ℕ) →
      π₀ (UnbasedPointedMapping.stageFiber K
        (PointedObject.basedHom CirclePower.space.{u} (iteratedLoopSpace r Y)) n).right ≃
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right r
            (UnbasedPointedMapping.stageFiber K Y n).basepoint
  | 0 => stageFiberLoopComponentEquiv K Y n
  | r + 1 => (stageFiberIteratedLoopComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r).trans
      (stageFiberLoopPositiveEquiv K Y n r).toEquiv

/-- 概要：全正次数の既存の係数表示は反復 loop 値の成分係数と正符号で可換。
方針：基本群の可換式から出発し、一段の loop の係数公式で帰納する。
規約：各非退化セルで係数の値そのものを比較する。連結準同型は別に比較する。
使われ方：Goerss–Jardine VIII §1。全高次数の微分の代表計算への入力。 -/
theorem stageFiberCoefficientEquiv_iteratedLoopComponent (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (a : π₀ (UnbasedPointedMapping.stageFiber K
      (PointedObject.basedHom CirclePower.space.{u} (iteratedLoopSpace r Y)) n).right)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K Y n r (stageFiberIteratedLoopComponentEquiv K Y n r a) s =
      iteratedLoopGroupEquiv Y (n + 1) r
        (CirclePower.positiveHomotopyEquiv (iteratedLoopSpace r Y) n
          (stageFiberComponentEquiv K
            (PointedObject.basedHom CirclePower.space.{u} (iteratedLoopSpace r Y)) n a s)) := by
  induction r generalizing Y with
  | zero => exact stageFiberCoefficientEquiv_loopComponent K Y n a s
  | succ r ih =>
    change stageFiberCoefficientEquiv K Y n (r + 1)
      (stageFiberLoopPositiveEquiv K Y n r
        (stageFiberIteratedLoopComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r a)) s = _
    rw [stageFiberCoefficientEquiv_loopPositive, ih (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)]
    rfl

end SkeletalCellAttachment
end
end SerrePositivity.KST.Spectra
