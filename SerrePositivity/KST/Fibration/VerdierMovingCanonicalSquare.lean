module
public import SerrePositivity.KST.Fibration.VerdierMovingCanonicalSharedDiagonal
public import SerrePositivity.KST.Fibration.VerdierNormalizedSquareFamily

/-!
概要：同じ実読出しの上下 canonical 族を、全 native Hom を保持して四角柱へ貼る。
方針：同じ実入力から得た厳密共有対角を所有する四角柱構成へ渡す。
規約：元の下側への可逆比較を保持し、厳密切断と新たな存在仮定を使わない。
使われ方：K-6 c4 の指定有限端点照合の共通の実四角柱。
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
section Input
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)
  (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

variable
  (H : SSet.Homotopy
    ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))
    (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (verdierNativeCompositePoint d 1)))
  (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (verdierReadoutUpperComparison d)
    (verdierLowerNativeReadoutHomotopy d L hL) H)
  (hT : T.diagram ≫ (pre verdierReadoutPathBoundary.{u}).app _ =
    curry (verdierReadoutBoundaryDiagram d L hL hfull))
include hT


/-- 概要：元の同じ実読出しから得た上下族の全四角柱。
方針：正規化下側と動く上側の厳密共有対角で貼る。
規約：全 native Hom と元の下側への可逆比較を保持する。
使われ方：両有限端点と縦辺の照合。 -/
def verdierMovingCanonicalSquareFamily :
    ((Δ[1] ⊗ Δ[1]) ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  verdierNormalizedSquareFamily
    (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull))
    (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
    (verdierMovingCanonicalSharedDiagonal d L hL hfull H T hT)

/-- 概要：同じ実四角柱の上側は元の動く canonical 全族。
方針：押し出しの厳密制限を回収する。
規約：全時刻・全次数の等式。使われ方：上側有限端点への接続。 -/
theorem verdierMovingCanonicalSquareFamily_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierMovingCanonicalSquareFamily d L hL hfull H T hT =
      verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT) :=
  verdierNormalizedSquareFamily_upper _ _ _

/-- 概要：同じ実四角柱の下側は同じ読出しの正規化下側全族。
方針：押し出しの厳密制限を回収する。
規約：元の族との厳密一致は要求しない。使われ方：下側有限端点への接続。 -/
theorem verdierMovingCanonicalSquareFamily_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierMovingCanonicalSquareFamily d L hL hfull H T hT =
      verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull) :=
  verdierNormalizedSquareFamily_lower _ _ _
end Input

/-- 概要：全 native Hom を保持する正規化下側付きの実四角柱は存在する。
方針：同じ実読出しと相対合成を一度だけ選び、同じ上下族を貼る。
規約：供給命題の追加仮定なし。元の下側との可逆比較も同時に保持する。
使われ方：残る有限端点の外延性と全四角形比較への実入力。 -/
theorem verdierMovingCanonicalSquareFamily_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∃ (N F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (Q : ((Δ[1] ⊗ Δ[1]) ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierFullSLowerDeformation d).h N) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N =
        fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ F = verdierMovingUpperHorn d ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫ Q = F ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫ Q = N ∧
      ∀ k : (Δ[1] : SSet.{u + 1}) _⦋0⦌,
        HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex N k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h k)).map
              ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  obtain ⟨L, hfull, hL⟩ := verdierLowerNativeReadoutRecovery_exists d
  obtain ⟨H, T, hT⟩ := verdierReadoutRelativeComposition_exists d L hL hfull
  exact ⟨_, _, verdierMovingCanonicalSquareFamily d L hL hfull H T hT,
    ⟨verdierLowerCanonicalFamily_iso d (verdierLowerCanonicalReadout d L hfull)⟩,
    verdierLowerCanonicalFamily_horn d (verdierLowerCanonicalReadout d L hfull),
    verdierMovingUpperFamily_horn d (verdierReadoutMovingLongInput d L hL hfull H T hT),
    verdierMovingCanonicalSquareFamily_upper d L hL hfull H T hT,
    verdierMovingCanonicalSquareFamily_lower d L hL hfull H T hT,
    verdierLowerCanonicalReadout_native d L hfull hL⟩

end SerrePositivity.KST.Fibration
