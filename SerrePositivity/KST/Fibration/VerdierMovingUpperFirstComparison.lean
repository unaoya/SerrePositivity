module
public import SerrePositivity.KST.Fibration.VerdierUpperNativeOriginalCoordinates
public import SerrePositivity.KST.Fibration.VerdierMovingUpperVertices

/-!
概要：動く上側の同じ始端と実 (9b) 欠面で、二短辺と全 native 長 Hom を照合する。
方針：同じ元の両端を短辺から回収し、native 読出しの座標を戻す。
規約：有限二胞体の外延性自体は F1 正本に残す。新たな存在仮定を追加しない。
使われ方：K-6 c4 の指定有限二胞体同定への三つの実入力。
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

/-- 概要：同じ指定両端での native Hom 読出し頂点の HEq は元の全 Hom の HEq を反映する。
方針：関手頂点の単射性と元の宇宙持ち上げの忠実性を合成する。
規約：両端の等号は明示し、新たな存在を要求しない。
使われ方：K-6 c4 の両有限端点の全 native Hom 座標照合。 -/
theorem verdierNativeReadout_vertex_heq {A B A' B' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (hA : A = A') (hB : B = B')
    (f : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ SimplicialCategory.sHom A B)
    (g : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ SimplicialCategory.sHom A' B')
    (h : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map g))) : HEq f g := by
  cases hA
  cases hB
  have hm : (SSet.uliftFunctor.{u + 1, u}).map f = (SSet.uliftFunctor.{u + 1, u}).map g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective (eq_of_heq h)
  exact ((SSet.uliftFunctor.{u + 1, u}).map_injective hm).heq

/-- 概要：同じ始端二胞体と実制御欠面の第一面は厳密一致。
方針：元の全一単体として回収した第一短辺を同じ二胞体面の単体へ戻す。
規約：元の有限二胞体を保持。使われ方：F1 外延性の第一短辺条件。 -/
theorem verdierMovingUpperFamily_first_controlled_delta_two
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
        (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1}))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
  apply SSet.yonedaEquiv.symm.injective
  simpa only [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply] using
    verdierMovingUpperFamily_first_controlled_firstFace d ℓ

/-- 概要：同じ始端二胞体と実制御欠面の第二面は厳密一致。
方針：元の全一単体として回収した第二短辺を同じ二胞体面の単体へ戻す。
規約：元の有限二胞体を保持。使われ方：F1 外延性の第二短辺条件。 -/
theorem verdierMovingUpperFamily_first_controlled_delta_zero
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
        (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1}))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
  apply SSet.yonedaEquiv.symm.injective
  simpa only [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply] using
    verdierMovingUpperFamily_first_controlled_lastFace d ℓ

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



/-- 概要：同じ再構成始端の全 native Hom は元の指定上側二胞体の native Hom 自身。
方針：同じ短辺から回収した両端座標と元の全読出しの HEq を戻す。
規約：群作用や直接端だけの一致へ弱めない。使われ方：制御欠面との全長 Hom 照合。 -/
theorem verdierMovingUpperFamily_first_original_native :
    HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
        (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌)
        (verdierUpperTriangle d)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  let ℓ := verdierReadoutMovingLongInput d L hL hfull H T hT
  have hs : (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).obj ⟨ULift.up 0⟩ =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌)
        (verdierUpperTriangle d)).obj ⟨ULift.up 0⟩) := by
    change _ = stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)
    exact (verdierMovingUpperFamily_source d ℓ _).trans
      (congrArg (fun A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} => stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
        ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))).symm
  have ht : (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).obj ⟨ULift.up 2⟩ =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌)
        (verdierUpperTriangle d)).obj ⟨ULift.up 2⟩) := by
    change _ = stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)
    exact (verdierMovingUpperFamily_target d ℓ _).trans
      (congrArg (fun C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} => stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C))
        ((verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq))).symm
  exact verdierNativeReadout_vertex_heq hs ht _ _
    ((verdierMovingUpperFamily_first_native d L hL hfull H T hT).symm.trans
      (verdierOriginalNativeHomFamily_upper_heq d).symm)

/-- 概要：同じ再構成始端と実 (9b) 制御欠面の全 native 長 Hom は一致する。
方針：双方を元の同じ指定上側二胞体の native Hom へ照合する。
規約：二短辺も既存の厳密回収を保持する。
使われ方：F1 の有限二胞体外延性への第三入力。 -/
theorem verdierMovingUpperFamily_first_controlled_native :
    HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
        (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
        (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1}))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) :=
  (verdierMovingUpperFamily_first_original_native d L hL hfull H T hT).trans
    (zeroMiddleNativeUpperFamily_native (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1})
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).symm

end SerrePositivity.KST.Fibration
