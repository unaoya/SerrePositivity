module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.LeftFibrationTerminalFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalCosliceSource
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatTensorAndArrowObjects
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TensorInitialVertices

/-!
概要：元の商四角形全体を、同じ左下頂点の coslice 内の全図式へ戻す。
方針：正方形の左下始対象から恒等図式を持ち上げ、同じ元の四角形で後合成する。
規約：元の四角形は全単体で保持し、左下頂点への錐の脚の可逆性も証明する。
使われ方：二つの元の実矢印に対する右分数添付の商錐を、新仮定なしに供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 元の正方形の左下頂点。 -/
def fractionSquareInitialVertex : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
  (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 元の四角形の同じ左下点。 -/
def fractionSquarePoint {X : SSet.{u}} (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    (Δ[0] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex ≫ F

/-- 元の四角形を全体として保持し、元の左下点の可逆な錐の脚を持つ coslice 図式。 -/
structure SquareCosliceSeed {X : SSet.{u}} (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) where
  lift : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F)
  projection : lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) = F
  initial_isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry lift,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection lift).trans projection⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F)
      _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex)

/-- 元の四角形から、同じ全図式・左下点・可逆な左下錐脚を持つ coslice 図式を構成する。 -/
lemma exists_squareCosliceSeed {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F) := by
  let Q : SSet.{u} := (Δ[1] : SSet.{u}) ⊗ Δ[1]
  let : Quasicategory Q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor _ _
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := Q) _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isInitialVertex_tensor _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanStdSimplex_first_isInitialVertex 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanStdSimplex_first_isInitialVertex 1)
  obtain ⟨U₀, hU₀⟩ := h₀.exists_cosliceLift (𝟙 Q)
  let c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (𝟙 Q) := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry U₀,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection U₀).trans hU₀⟩
  have hc₀ : c₀.vertex = _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex := by
    rw [c₀.vertex_eq]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry U₀) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed, Equiv.apply_symm_apply]
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c₀ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex
  let v' : Truncated.Edge (X := (truncation 2).obj Q)
      _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex :=
    ⟨v.edge, v.src_eq.trans hc₀, v.tgt_eq⟩
  have hv' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Q) v' :=
    isIso_of_isInitial h₀.isInitialHo h₀.isInitialHo _
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Q) v :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := v) (f := v') rfl).mpr hv'
  let U := U₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex) F
  have hU : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) = F := by
    dsimp only [U, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection, ← Category.assoc, hU₀,
      Category.id_comp]
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry U, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection U).trans hU⟩
  have hc : c.val = c₀.val ≫ F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp U₀ F
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex).edge =
      (v.map ((truncation 2).map F)).edge := by
    change c.val.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneDomainLeg _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex).edge = _
    rw [hc]
    rfl
  exact ⟨⟨U, hU, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hv.map F)⟩⟩

end SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_squareCosliceSeed := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.exists_squareCosliceSeed

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionSquareInitialVertex := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionSquarePoint := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.casesOn := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.ctorIdx := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.initial_isInvertible := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.initial_isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.lift (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.lift := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.lift

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.noConfusionType := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.noConfusionType

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.projection := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.projection

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.rec := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.recOn := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionSquareInitialVertex._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.inj := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.injEq := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed.mk.sizeOf_spec
