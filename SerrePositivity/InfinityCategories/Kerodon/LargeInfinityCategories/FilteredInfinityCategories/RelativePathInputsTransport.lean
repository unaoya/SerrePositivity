module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackBoundaryInputsTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiberwisePullbackBoundaryModelTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPathCollapseContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.NullHomotopyRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData

/-!
概要：元の境界引き戻し射と有限模型の底と二入力を、全境界の指定円柱を保って輸送する。
方針：底の共通収縮と境界輸送を選び、その両端を二入力の相対輸送へ渡す。
規約：元の境界の終点、三座標の全円柱、模型の底の全円柱を保持する。
使われ方：有限模型の全相対境界輸送の構成。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：境界の元の引き戻し射と二入力の全輸送を、有限模型の底に整合させて構成する。
方針：部分 path を潰した共通底の収縮を、二入力の境界固定輸送へ渡す。
規約：追加の持ち上げデータは仮定しない。使われ方：標的有限模型の相対輸送の入力。 -/
lemma exists_relativePathInputTransportData {K M E D H B : SSet.{u}}
    [K.Finite] [M.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f ≫ p)] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g)
    (m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M) (q : M ⟶ H)
    (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 0 ≫ m) ≫ q = u ≫ f)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 1 ≫ m) ≫ q = v ≫ g) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q) := by
  obtain ⟨b, t, Hq, L, hPath⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.fiberwisePullback_boundary_model_transport p f g a
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) q hk
  let j₀ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 0 ≫ m
  let j₁ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 1 ≫ m
  have hj₀ : j₀ ≫ (q ≫ p) = u ≫ (f ≫ p) := by
    dsimp only [j₀]
    rw [← Category.assoc, h₀, Category.assoc]
  have hj₁ : j₁ ≫ (q ≫ p) = v ≫ (g ≫ p) := by
    dsimp only [j₁]
    rw [← Category.assoc, h₁, Category.assoc]
  let H₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nullHomotopyRestriction Hq j₀ hj₀
  let H₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nullHomotopyRestriction Hq j₁ hj₁
  have he₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) = A.ι ≫ j₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide_endpoint, Category.assoc]
  have he₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) = A.ι ≫ j₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide_endpoint, Category.assoc]
  have hH₀ : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ H₀.h =
      L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.collapsedPathCylinder_endpoint (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) A.ι j₀ 0 he₀ Hq.h
      (L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) hPath
  have hH₁ : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ H₁.h =
      L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.collapsedPathCylinder_endpoint (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) A.ι j₁ 1 he₁ Hq.h
      (L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) hPath
  obtain ⟨s, r, hs, hr, U, V, hU, hV, hUp, hVp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullback_boundary_inputs_transport p f g A.ι a u v hu hv b t L H₀ H₁ hH₀ hH₁
  exact ⟨{
    vertex := b
    boundaryValue := t
    modelBase := Hq
    boundaryHomotopy := L
    leftValue := s
    rightValue := r
    leftHomotopy := U
    rightHomotopy := V
    boundary_left := hs
    boundary_right := hr
    left_restrict := hU
    right_restrict := hV
    left_projection := hUp
    right_projection := hVp
    path_projection := hPath }⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
