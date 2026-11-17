# F1 native 二胞体外延性の利用側（K-B）

- 供給依頼の型は [元の依頼](L3-native-triangle-ext-request.md:19)。
- 下記は F1 の外延性を引数に取る利用側の型検査済みコード。外延性の証明・公理・新しい存在仮定を K-B 主経路に追加しない。
- 同じ実読出し・相対合成・上下 canonical 族の四端点を同定し、同じ実 (9b) 制御四角柱と正規化四角柱を合成して元の商核へ戻す。
- 検証：`lake env lean /tmp/kb-moving-canonical-finite-ext-consumer.lean`、終了 0。実 F1 公開名が届けば引数への実代入で所有葉へ接続する。

```lean
import SerrePositivity.KST.Fibration.VerdierMovingCanonicalSquareComparison
import SerrePositivity.KST.Fibration.VerdierLowerCanonicalFiniteFaces
import SerrePositivity.KST.Fibration.VerdierMovingUpperLastComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Fibration
variable (hExt : ∀ F G : SpaceInfinity.{u} _⦋2⦌,
  SpaceInfinity.δ (0 : Fin 3) F = SpaceInfinity.δ (0 : Fin 3) G →
  SpaceInfinity.δ (2 : Fin 3) F = SpaceInfinity.δ (2 : Fin 3) G →
  HEq (F.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) (G.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) → F = G)
variable (d : VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)
  (hfull : L ≫ evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

variable
  (H : SSet.Homotopy
    ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))
    (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))
      (verdierNativeCompositePoint d 1)))
  (T : FunctorCompositionTriangle (verdierReadoutUpperComparison d)
    (verdierLowerNativeReadoutHomotopy d L hL) H)
  (hT : T.diagram ≫ (pre verdierReadoutPathBoundary.{u}).app _ =
    curry (verdierReadoutBoundaryDiagram d L hL hfull))
include hT


include hExt

def kbMovingCanonicalFiniteExtConsumer :
    FunctorIso (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection) := by
  let ℓ := verdierReadoutMovingLongInput d L hL hfull H T hT
  let n := verdierLowerCanonicalReadout d L hfull
  have hU₀ : familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1]) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    exact hExt _ _ (verdierMovingUpperFamily_first_controlled_delta_zero d ℓ)
      (verdierMovingUpperFamily_first_controlled_delta_two d ℓ)
      (verdierMovingUpperFamily_first_controlled_native d L hL hfull H T hT)
  have hN₀ : familyAtVertex (verdierLowerCanonicalFamily d n)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) := by
    apply SSet.yonedaEquiv.injective
    exact (hExt _ _ (verdierLowerCanonicalFamily_first_delta_zero d n)
      (verdierLowerCanonicalFamily_first_delta_two d n)
      (verdierLowerCanonicalReadout_first_native d L hfull hL)).trans
        ((SSet.yonedaEquiv (X := SpaceInfinity.{u})).apply_symm_apply _).symm
  have hU₁ : familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (verdierMovingUpperLastTriangle d).simplex := by
    apply SSet.yonedaEquiv.injective
    exact (hExt _ _ (verdierMovingUpperFamily_last_standard_delta_zero d ℓ)
      (verdierMovingUpperFamily_last_standard_delta_two d ℓ)
      (verdierMovingUpperFamily_last_standard_native d L hL hfull H T hT)).trans
        ((SSet.yonedaEquiv (X := SpaceInfinity.{u})).apply_symm_apply _).symm
  have hN₁ : familyAtVertex (verdierLowerCanonicalFamily d n)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (coherentSimplexMaximalization (verdierFullSLowerSimplex d)) := by
    apply SSet.yonedaEquiv.injective
    exact (hExt _ _ (verdierLowerCanonicalFamily_last_delta_zero d n)
      (verdierLowerCanonicalFamily_last_delta_two d n)
      (verdierLowerCanonicalReadout_last_native d L hfull hL)).trans
        ((SSet.yonedaEquiv (X := SpaceInfinity.{u})).apply_symm_apply _).symm
  exact verdierMovingCanonicalKernelSquareIso d L hL hfull H T hT hU₀ hN₀ hU₁ hN₁

```
