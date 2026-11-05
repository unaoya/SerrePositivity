module
public import SerrePositivity.KST.Fibration.VerdierReadoutBoundaryDiagram
public import SerrePositivity.KST.Fibration.VerdierReadoutPathBoundary
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalBoundaryExt
public import SerrePositivity.InfinityCategories.F1B.RoofRelativeCompositionTriangle

/-!
概要：元の二つの全長 Hom 比較を、同じ直接端・合成端境界二単体を固定して合成する。
方針：元の native path 境界と実境界図式を既存の相対合成持ち上げへ代入する。
規約：同じ下側読出しを保持し、新しい存在仮定や厳密切断を使わない。
使われ方：K-6 c4 の動く第二短辺と整合する上側全長 Hom 族の入力。
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
variable (d : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u})

private theorem readoutComponentCurve
    {f g : (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}) ⟶
      verdierNativeLongHomTarget d}
    (H : SSet.Homotopy f g)
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u})) _⦋0⦌) :
    SSet.yonedaEquiv.symm (simplicialHomotopyVertexEdge H x).edge =
      lift (SSet.const x) (𝟙 (Δ[1] : SSet.{u + 1})) ≫ H.h := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change H.h.app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve TriangleNativePath.{u}))) x).edge, homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋1⦌)
      (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})))
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) =
      homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [pinchedConstant_one, hi]

/-- 概要：元の実長 Hom ホモトピーの指定成分を全区間の実制限へ戻す。
方針：同じ元の一単体の Yoneda 表示を回収する。
規約：同じ Verdier 両端と全 path 入力を保持する。
使われ方：相対合成の直接端を同じ下側読出しへ照合する。 -/
theorem verdierReadoutComponentCurve
    {f g : (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}) ⟶
      verdierNativeLongHomTarget d}
    (H : SSet.Homotopy f g)
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u})) _⦋0⦌) :
    SSet.yonedaEquiv.symm (simplicialHomotopyVertexEdge H x).edge =
      lift (SSet.const x) (𝟙 (Δ[1] : SSet.{u + 1})) ≫ H.h :=
  readoutComponentCurve d H x

variable
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)
  (hfull : L ≫ evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

/-- 概要：実境界図式の面零は同じ読出し全族の native path 境界への制限。
方針：同じ二端点の実成分回収を全境界の外延性へ代入する。
規約：全一単体の非退化成分も含む写像の等式。
使われ方：相対合成持ち上げの右短辺の面適合条件。 -/
theorem verdierReadoutBoundaryDiagram_last_restriction :
    ((boundary 1 : SSet.{u + 1}) ◁ stdSimplex.δ (0 : Fin 3)) ≫
      verdierReadoutBoundaryDiagram d L hL hfull =
      (verdierReadoutPathBoundary.{u} ▷ (Δ[1] : SSet.{u + 1})) ≫
        (verdierLowerNativeReadoutHomotopy d L hL).h := by
  rw [verdierReadoutBoundaryDiagram_last]
  apply F2.intervalBoundary_hom_ext
  · rw [intervalBoundaryDiagram_zero, ← Category.assoc, verdierReadoutPathBoundary_zero]
    exact readoutComponentCurve d _ _
  · rw [intervalBoundaryDiagram_one, ← Category.assoc, verdierReadoutPathBoundary_one]
    exact readoutComponentCurve d _ _

/-- 概要：実境界図式の面二は同じ全 S• 比較の native path 境界への制限。
方針：同じ元の二成分を全境界の外延性で貼る。
規約：同じ全 S• 円柱と全境界を保持する。
使われ方：相対合成持ち上げの左短辺の面適合条件。 -/
theorem verdierReadoutBoundaryDiagram_first_restriction :
    ((boundary 1 : SSet.{u + 1}) ◁ stdSimplex.δ (2 : Fin 3)) ≫
      verdierReadoutBoundaryDiagram d L hL hfull =
      (verdierReadoutPathBoundary.{u} ▷ (Δ[1] : SSet.{u + 1})) ≫
        (verdierReadoutUpperComparison d).h := by
  rw [verdierReadoutBoundaryDiagram_first]
  apply F2.intervalBoundary_hom_ext
  · rw [intervalBoundaryDiagram_zero, ← Category.assoc, verdierReadoutPathBoundary_zero]
    exact readoutComponentCurve d _ _
  · rw [intervalBoundaryDiagram_one, ← Category.assoc, verdierReadoutPathBoundary_one]
    exact readoutComponentCurve d _ _

/-- 概要：同じ読出しと全 S• 比較は、指定された二端点の合成二単体を保って合成できる。
方針：元の実境界図式と二面の厳密一致を D 正本の相対合成へ渡す。
規約：元の L とその全時刻合成端条件を保持し、供給命題引数を追加しない。
使われ方：K-6 c4 の直接端と動く合成端を同時に指定した実長 Hom 合成。 -/
theorem verdierReadoutRelativeComposition_exists :
    ∃ H : SSet.Homotopy
      ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))
      (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1)),
      ∃ T : FunctorCompositionTriangle (verdierReadoutUpperComparison d)
          (verdierLowerNativeReadoutHomotopy d L hL) H,
        T.diagram ≫ (pre verdierReadoutPathBoundary.{u}).app _ =
          curry (verdierReadoutBoundaryDiagram d L hL hfull) := by
  apply roofRelativeCompositionTriangle_exists verdierReadoutPathBoundary
    (verdierReadoutUpperComparison d) (verdierLowerNativeReadoutHomotopy d L hL)
    (curry (verdierReadoutBoundaryDiagram d L hL hfull))
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app, uncurry_curry]
    exact verdierReadoutBoundaryDiagram_last_restriction d L hL hfull
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app, uncurry_curry]
    exact verdierReadoutBoundaryDiagram_first_restriction d L hL hfull

end SerrePositivity.KST.Fibration
