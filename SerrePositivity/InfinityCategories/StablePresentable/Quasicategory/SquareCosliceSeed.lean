module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.InitialHomotopy
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.LeftFibrationTerminalFiber
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalCosliceSource
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatTensorAndArrowObjects
public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorInitialVertices

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
namespace SerrePositivity.InfinityCategories.StablePresentable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

/-- 元の正方形の左下頂点。 -/
def fractionSquareInitialVertex : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
  (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 元の四角形の同じ左下点。 -/
def fractionSquarePoint {X : SSet.{u}} (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    (Δ[0] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex ≫ F

/-- 元の四角形を全体として保持し、元の左下点の可逆な錐の脚を持つ coslice 図式。 -/
structure SquareCosliceSeed {X : SSet.{u}} (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) where
  lift : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquarePoint F)
  projection : _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.lift ≫ sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquarePoint F) = F
  initial_isInvertible : IsInvertibleEdge (X := X)
    (F2.nativeConeLeg (⟨sliceUnderUncurry _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.lift,
      (sliceUnderUncurry_projection _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.lift).trans _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.projection⟩ : JoinCone F)
      _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex)

/-- 元の四角形から、同じ全図式・左下点・可逆な左下錐脚を持つ coslice 図式を構成する。 -/
lemma exists_squareCosliceSeed {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : Nonempty (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed F) := by
  let Q : SSet.{u} := (Δ[1] : SSet.{u}) ⊗ Δ[1]
  let : Quasicategory Q := F2.quasicategory_tensor _ _
  have h₀ : IsInitialVertex (X := Q) _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex :=
    F2.isInitialVertex_tensor _ _ (F1B.kanStdSimplex_first_isInitialVertex 1)
      (F1B.kanStdSimplex_first_isInitialVertex 1)
  obtain ⟨U₀, hU₀⟩ := h₀.exists_cosliceLift (𝟙 Q)
  let c₀ : JoinCone (𝟙 Q) := ⟨sliceUnderUncurry U₀,
    (sliceUnderUncurry_projection U₀).trans hU₀⟩
  have hc₀ : c₀.vertex = _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex := by
    rw [c₀.vertex_eq]
    change SSet.yonedaEquiv (joinInl Δ[0] Q ≫ sliceUnderUncurry U₀) = _
    rw [sliceUnderUncurry_fixed, Equiv.apply_symm_apply]
  let v := F2.nativeConeLeg c₀ _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex
  let v' : Truncated.Edge (X := (truncation 2).obj Q)
      _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex :=
    ⟨v.edge, v.src_eq.trans hc₀, v.tgt_eq⟩
  have hv' : IsInvertibleEdge (X := Q) v' :=
    isIso_of_isInitial h₀.isInitialHo h₀.isInitialHo _
  have hv : IsInvertibleEdge (X := Q) v :=
    (isInvertibleEdge_congr (e := v) (f := v') rfl).mpr hv'
  let U := U₀ ≫ sliceUnderPostcomp (SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex) F
  have hU : U ≫ sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquarePoint F) = F := by
    dsimp only [U, _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquarePoint]
    rw [Category.assoc, sliceUnderPostcomp_projection, ← Category.assoc, hU₀,
      Category.id_comp]
  let c : JoinCone F := ⟨sliceUnderUncurry U, (sliceUnderUncurry_projection U).trans hU⟩
  have hc : c.val = c₀.val ≫ F := sliceUnderUncurry_postcomp U₀ F
  have he : (F2.nativeConeLeg c _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex).edge =
      (v.map ((truncation 2).map F)).edge := by
    change c.val.app (Opposite.op ⦋1⦌)
      (F2.coneDomainLeg _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex).edge = _
    rw [hc]
    rfl
  exact ⟨⟨U, hU, (isInvertibleEdge_congr he).mpr (hv.map F)⟩⟩

end SerrePositivity.InfinityCategories.StablePresentable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_squareCosliceSeed := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.exists_squareCosliceSeed

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionSquareInitialVertex := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquarePoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionSquarePoint := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquarePoint

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.casesOn := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.ctorIdx := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.initial_isInvertible := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.initial_isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.lift (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.lift := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.lift

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.noConfusion := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.noConfusionType := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.noConfusionType

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.projection := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.projection

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.rec := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.recOn := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionSquareInitialVertex._proof_1 := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.fractionSquareInitialVertex._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.inj := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.injEq := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareCosliceSeed.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.SquareCosliceSeed.mk.sizeOf_spec
