module
public import SerrePositivity.KST.Fibration.VerdierLowerCanonicalFamily

/-!
概要：元の実下側読出しを同じ正規化下側の長 Hom 入力として保持する。
方針：全合成端の厳密回収を実 fiber 頂点へ渡す。
規約：読出しを再選択せず、正規化前後の全 native Hom を同じ入力で比較する。
使われ方：K-6 c4 の正規化下側と動く上側の共通入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

/-- 概要：同じ実読出しを正規化下側の実長 Hom fiber へ登録する。
方針：元の全合成端回収をそのまま使う。
規約：新しい存在仮定を追加しない。使われ方：実 canonical encoder への入力。 -/
def verdierLowerCanonicalReadout : (verdierLowerCanonicalLongSpace d) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomVertex
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) Δ[1]
    (verdierLowerReconstructionCompositeFamily d Δ[1]) L hfull

/-- 概要：正規化下側の入力から元の同じ読出し全族を厳密回収する。
方針：実 fiber 頂点の標準順逆比較を使う。
規約：各点に弱めない。使われ方：共有対角と native Hom の同時照合。 -/
theorem verdierLowerCanonicalReadout_value :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue (verdierLowerCanonicalReadout d L hfull) = L :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomVertex_value _ _ _ _ _ _

/-- 概要：同じ読出しを使う正規化下側は元の実下側の全 native Hom を各時刻で保持する。
方針：同じ実入力の native 回収と元の読出し回収を合成する。
規約：正規化前後の全族の厳密等号は主張しない。
使われ方：有限端点の二短辺・全 native Hom による二胞体照合。 -/
theorem verdierLowerCanonicalReadout_native
    (hL : VerdierLowerNativeReadoutRecovery d L)
    (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
        (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull)) k)).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k)).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have hn := verdierLowerCanonicalFamily_native d (verdierLowerCanonicalReadout d L hfull) k
  rw [verdierLowerCanonicalReadout_value] at hn
  exact hn.symm.trans (hL k)

end SerrePositivity.KST.Fibration
