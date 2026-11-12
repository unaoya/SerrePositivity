module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperFirstComparison
public import SerrePositivity.KST.Fibration.VerdierMovingUpperLastTriangle

/-!
概要：動く上側の同じ終端と元の標準合成二胞体で、二短辺と全 native 長 Hom を照合する。
方針：元の二短辺を保持し、同じ実合成端の native 定値回収を使う。
規約：有限二胞体の外延性は F1 正本に残し、新たな存在仮定を加えない。
使われ方：K-6 c4 の上側終端の有限二胞体同定への三つの実入力。
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

/-- 概要：同じ終端二胞体と元の標準合成二胞体の第一短辺面は厳密一致。
方針：元の実 core 包含の同じ coherent な辺を両側で回収する。
規約：元の有限二胞体を保持。使われ方：F1 外延性の第一短辺条件。 -/
theorem verdierMovingUpperFamily_last_standard_delta_two
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3) (verdierMovingUpperLastTriangle d).simplex := by
  have hm : stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (verdierMovingUpperLastTriangle d).simplex :=
    (verdierMovingUpperFamily_firstEdge d ℓ _).trans
      (verdierMovingUpperLastTriangle d).δ_two_yonedaEquiv_symm.symm
  have hs := stdSimplex.δ_comp_yonedaEquiv_symm (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) (2 : Fin 3)
  have ht := stdSimplex.δ_comp_yonedaEquiv_symm (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (verdierMovingUpperLastTriangle d).simplex (2 : Fin 3)
  have hr : SSet.yonedaEquiv.symm (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
    Equiv.symm_apply_apply _ _
  apply SSet.yonedaEquiv.symm.injective
  exact hs.symm.trans ((congrArg (fun f => stdSimplex.δ (2 : Fin 3) ≫ f) hr).trans (hm.trans ht))

/-- 概要：同じ終端二胞体と元の標準合成二胞体の第二短辺面は厳密一致。
方針：元の実包含・商の全 S• 合成作用を両側で同じ coherent 辺へ戻す。
規約：元の実完全射を保持。使われ方：F1 外延性の第二短辺条件。 -/
theorem verdierMovingUpperFamily_last_standard_delta_zero
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3) (verdierMovingUpperLastTriangle d).simplex := by
  have hm : stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm (verdierMovingUpperLastTriangle d).simplex :=
    (verdierMovingUpperFamily_last_lastEdge d ℓ).trans
      (verdierMovingUpperLastTriangle d).δ_zero_yonedaEquiv_symm.symm
  have hs := stdSimplex.δ_comp_yonedaEquiv_symm (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) (0 : Fin 3)
  have ht := stdSimplex.δ_comp_yonedaEquiv_symm (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (verdierMovingUpperLastTriangle d).simplex (0 : Fin 3)
  have hr : SSet.yonedaEquiv.symm (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
    Equiv.symm_apply_apply _ _
  apply SSet.yonedaEquiv.symm.injective
  exact hs.symm.trans ((congrArg (fun f => stdSimplex.δ (0 : Fin 3) ≫ f) hr).trans (hm.trans ht))

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



/-- 概要：同じ再構成終端と元の標準合成二胞体の全 native 長 Hom は一致する。
方針：両側を同じ元の実合成端の定値全族へ戻し、同じ両端の読出しを反映する。
規約：二短辺の厳密一致も保持。使われ方：F1 の有限二胞体外延性への第三入力。 -/
theorem verdierMovingUpperFamily_last_standard_native :
    HEq ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
        (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      ((verdierMovingUpperLastTriangle d).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  let ℓ := verdierReadoutMovingLongInput d L hL hfull H T hT
  have hs : (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).obj ⟨ULift.up 0⟩ =
      (verdierMovingUpperLastTriangle d).simplex.obj ⟨ULift.up 0⟩ := by
    exact verdierMovingUpperFamily_source d ℓ _
  have ht : (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).obj ⟨ULift.up 2⟩ =
      (verdierMovingUpperLastTriangle d).simplex.obj ⟨ULift.up 2⟩ := by
    exact verdierMovingUpperFamily_target d ℓ _
  have hc := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (verdierMovingUpperLastTriangle_native d)
  exact verdierNativeReadout_vertex_heq hs ht _ _
    ((verdierMovingUpperFamily_last_native d L hL hfull H T hT).symm.trans hc.symm.heq)

end SerrePositivity.KST.Fibration
