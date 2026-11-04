module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の正方形の左下頂点。 -/
def fractionSquareInitialVertex : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
  (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 元の四角形の同じ左下点。 -/
def fractionSquarePoint {X : SSet.{u}} (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    (Δ[0] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm fractionSquareInitialVertex ≫ F

/-- 元の四角形を全体として保持し、元の左下点の可逆な錐の脚を持つ coslice 図式。 -/
structure SquareCosliceSeed {X : SSet.{u}} (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) where
  lift : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder (fractionSquarePoint F)
  projection : lift ≫ sliceUnderProjection (fractionSquarePoint F) = F
  initial_isInvertible : IsInvertibleEdge (X := X)
    (F2.nativeConeLeg (⟨sliceUnderUncurry lift,
      (sliceUnderUncurry_projection lift).trans projection⟩ : JoinCone F)
      fractionSquareInitialVertex)

/-- 元の四角形から、同じ全図式・左下点・可逆な左下錐脚を持つ coslice 図式を構成する。 -/
lemma exists_squareCosliceSeed {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) : Nonempty (SquareCosliceSeed F) := by
  let Q : SSet.{u} := (Δ[1] : SSet.{u}) ⊗ Δ[1]
  let : Quasicategory Q := F2.quasicategory_tensor _ _
  have h₀ : IsInitialVertex (X := Q) fractionSquareInitialVertex :=
    F2.isInitialVertex_tensor _ _ (F1B.kanStdSimplex_first_isInitialVertex 1)
      (F1B.kanStdSimplex_first_isInitialVertex 1)
  obtain ⟨U₀, hU₀⟩ := h₀.exists_cosliceLift (𝟙 Q)
  let c₀ : JoinCone (𝟙 Q) := ⟨sliceUnderUncurry U₀,
    (sliceUnderUncurry_projection U₀).trans hU₀⟩
  have hc₀ : c₀.vertex = fractionSquareInitialVertex := by
    rw [c₀.vertex_eq]
    change SSet.yonedaEquiv (joinInl Δ[0] Q ≫ sliceUnderUncurry U₀) = _
    rw [sliceUnderUncurry_fixed, Equiv.apply_symm_apply]
  let v := F2.nativeConeLeg c₀ fractionSquareInitialVertex
  let v' : Truncated.Edge (X := (truncation 2).obj Q)
      fractionSquareInitialVertex fractionSquareInitialVertex :=
    ⟨v.edge, v.src_eq.trans hc₀, v.tgt_eq⟩
  have hv' : IsInvertibleEdge (X := Q) v' :=
    isIso_of_isInitial h₀.isInitialHo h₀.isInitialHo _
  have hv : IsInvertibleEdge (X := Q) v :=
    (isInvertibleEdge_congr (e := v) (f := v') rfl).mpr hv'
  let U := U₀ ≫ sliceUnderPostcomp (SSet.yonedaEquiv.symm fractionSquareInitialVertex) F
  have hU : U ≫ sliceUnderProjection (fractionSquarePoint F) = F := by
    dsimp only [U, fractionSquarePoint]
    rw [Category.assoc, sliceUnderPostcomp_projection, ← Category.assoc, hU₀,
      Category.id_comp]
  let c : JoinCone F := ⟨sliceUnderUncurry U, (sliceUnderUncurry_projection U).trans hU⟩
  have hc : c.val = c₀.val ≫ F := sliceUnderUncurry_postcomp U₀ F
  have he : (F2.nativeConeLeg c fractionSquareInitialVertex).edge =
      (v.map ((truncation 2).map F)).edge := by
    change c.val.app (Opposite.op ⦋1⦌)
      (F2.coneDomainLeg fractionSquareInitialVertex).edge = _
    rw [hc]
    rfl
  exact ⟨⟨U, hU, (isInvertibleEdge_congr he).mpr (hv.map F)⟩⟩

end SerrePositivity.KST.LocalizingInvariants
