module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundaryEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseBoundaryIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseRestrictionLifting

/-!
概要：底を固定した path の元の両端評価は、fiber ごとの積への left fibration。
方針：二点への制限と境界全空間の積表示を合成し、元の二評価と照合する。
規約：始点・終点と底射は元のもの。
使われ方：fiber ごとの path 引き戻しの相対有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：定値底の path の両端を同じ底の二対象の組に送る。
方針：元の両端の底射の一致で引き戻しへ持ち上げる。
規約：第一成分が始点。使われ方：両端を指定した相対持ち上げ問題。 -/
def fiberwiseIntervalEndpointPair {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p (Δ[1] : SSet.{u}) ⟶ pullback p p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1) (by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint_projection, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint_projection])

/-- 概要：元の両端評価の組は、二点への制限と境界の積同型の合成そのもの。
方針：境界の積同型を両成分で読み、元の端点制限式へ戻す。
規約：元の二射影を保持。使われ方：両端評価への持ち上げ性の輸送。 -/
lemma fiberwiseIntervalEndpointPair_restriction {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseBoundaryIso p).hom =
      fiberwiseIntervalEndpointPair p := by
  have h : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseBoundaryIso p).hom) ≫
      lift (pullback.fst p p) (pullback.snd p p) =
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram Δ[1] B) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair E := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseBoundaryIso_hom_product, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction_fst, Category.assoc]
    change pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram Δ[1] B) ≫
      ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι).app E ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowBoundaryEvaluationIso E).hom) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_restriction]
  apply pullback.hom_ext (f := p) (g := p)
  · rw [fiberwiseIntervalEndpointPair, pullback.lift_fst]
    have h₀ := congrArg (fun z ↦ z ≫ fst E E) h
    simpa only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans] using h₀
  · rw [fiberwiseIntervalEndpointPair, pullback.lift_snd]
    have h₁ := congrArg (fun z ↦ z ≫ snd E E) h
    simpa only [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans] using h₁

/-- 概要：元の底を固定した両端評価は left fibration。
方針：二点への単射制限の left fibration 性と境界の積同型を合成する。
規約：底の充填性は不要。使われ方：両端と底を保つ相対ホーンの持ち上げ。 -/
instance fiberwiseIntervalEndpointPair_leftFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (fiberwiseIntervalEndpointPair p) := by
  rw [← fiberwiseIntervalEndpointPair_restriction]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι))
    (MorphismProperty.of_isIso _ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseBoundaryIso p).hom)⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
