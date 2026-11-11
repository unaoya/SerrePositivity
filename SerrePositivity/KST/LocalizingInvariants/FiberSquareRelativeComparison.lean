module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FiberSquareRelativeComparison

public import SerrePositivity.KST.LocalizingInvariants.FiberSquareRightUniqueness
public import SerrePositivity.KST.LocalizingInvariants.ZeroCospanRelativeIso
public import SerrePositivity.KST.LocalizingInvariants.FiberConeRelativeIso
public import SerrePositivity.KST.LocalizingInvariants.FunctorIsoCancelPrecomp

/-!
概要：同じ右辺を持つ二つの fiber 正方形を、右辺で恒等となる元の全図式同型で比較する。
方針：零 cospan の恒等第一枝を普遍錐へ持ち上げ、同じ比較を正方形へ戻す。
規約：相対条件を型に保持してから選択する。使われ方：接続射と正規化の同じ選択。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberComparison

variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] {x y : X _⦋0⦌}
  {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f)

structure RelativeFunctorIso where
  iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.square t.square
  right_arrow : Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge iso.hom) =
    Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))))

omit [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] in
def relativeFunctorIso : RelativeFunctorIso s t := by
  letI : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X := ⟨⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1, s.zero_corner⟩⟩
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square
  have hF : horn₂₂.ι₀₂ ≫ F = SSet.yonedaEquiv.symm f.edge :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cospan_right_map s.square).trans s.right_edge
  have hG : horn₂₂.ι₀₂ ≫ G = SSet.yonedaEquiv.symm f.edge :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cospan_right_map t.square).trans t.right_edge
  let z := ZeroCospan.firstRelativeIso F G (FiberSquareHomotopy.cospan_zeroSecond s.toZeroTriangle)
    (FiberSquareHomotopy.cospan_zeroSecond t.toZeroTriangle) _ hF hG
  let a := FiberCone.relativeDiagramIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone s.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)
    s.isPullback t.isPullback z.iso
  let α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ s.square)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ t.square) := a.iso
  let e := cancelPrecompIso _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso α
  refine ⟨e, ?_⟩
  have h₀ := homPre_arrow_congr _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (cancelPrecompIso_arrow _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso α)
  have h₁ : Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv α.hom)) =
      Arrow.mk (homPre horn₂₂.ι₀₂ (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (horn 2 2 : SSet.{u})) α.hom)) := by
    rw [← homPre_comp, ← homPre_comp]
    exact congrArg (fun k ↦ Arrow.mk (homPre k α.hom)) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cospanConeSquareIso_inv_rightEdge
  exact h₀.trans (h₁.trans ((homPre_arrow_congr horn₂₂.ι₀₂ a.base_arrow).trans z.first_arrow))

end SerrePositivity.KST.LocalizingInvariants.FiberComparison
