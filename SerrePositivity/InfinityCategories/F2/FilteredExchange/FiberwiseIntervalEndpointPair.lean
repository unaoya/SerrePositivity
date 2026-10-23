module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseRestrictionLifting
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseBoundaryIso

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値底の path の両端を同じ底の二対象の組に送る。
方針：元の両端の底射の一致で引き戻しへ持ち上げる。
規約：第一成分が始点。使われ方：両端を指定した相対持ち上げ問題。 -/
def fiberwiseIntervalEndpointPair {E B : SSet.{u}} (p : E ⟶ B) :
    fiberwiseFunctorSpace p (Δ[1] : SSet.{u}) ⟶ pullback p p :=
  pullback.lift (fiberwiseIntervalEndpoint p 0) (fiberwiseIntervalEndpoint p 1) (by
    rw [fiberwiseIntervalEndpoint_projection, fiberwiseIntervalEndpoint_projection])

/-- 概要：元の両端評価の組は、二点への制限と境界の積同型の合成そのもの。
方針：境界の積同型を両成分で読み、元の端点制限式へ戻す。
規約：元の二射影を保持。使われ方：両端評価への持ち上げ性の輸送。 -/
lemma fiberwiseIntervalEndpointPair_restriction {E B : SSet.{u}} (p : E ⟶ B) :
    fiberwiseFunctorRestriction p arrowBoundaryι ≫ (fiberwiseBoundaryIso p).hom =
      fiberwiseIntervalEndpointPair p := by
  have h : (fiberwiseFunctorRestriction p arrowBoundaryι ≫ (fiberwiseBoundaryIso p).hom) ≫
      lift (pullback.fst p p) (pullback.snd p p) =
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
          arrowEndpointPair E := by
    rw [Category.assoc, fiberwiseBoundaryIso_hom_product, ← Category.assoc,
      fiberwiseFunctorRestriction_fst, Category.assoc]
    change pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
      ((pre arrowBoundaryι).app E ≫ (arrowBoundaryEvaluationIso E).hom) = _
    rw [← arrowEndpointPair_restriction]
  apply pullback.hom_ext (f := p) (g := p)
  · rw [fiberwiseIntervalEndpointPair, pullback.lift_fst]
    have h₀ := congrArg (fun z ↦ z ≫ fst E E) h
    simpa only [Category.assoc, lift_fst, arrowEndpointPair, fiberwiseIntervalEndpoint,
      intervalEndpointNatTrans] using h₀
  · rw [fiberwiseIntervalEndpointPair, pullback.lift_snd]
    have h₁ := congrArg (fun z ↦ z ≫ snd E E) h
    simpa only [Category.assoc, lift_snd, arrowEndpointPair, fiberwiseIntervalEndpoint,
      intervalEndpointNatTrans] using h₁

/-- 概要：元の底を固定した両端評価は left fibration。
方針：二点への単射制限の left fibration 性と境界の積同型を合成する。
規約：底の充填性は不要。使われ方：両端と底を保つ相対ホーンの持ち上げ。 -/
instance fiberwiseIntervalEndpointPair_leftFibration {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] : LeftFibration (fiberwiseIntervalEndpointPair p) := by
  rw [← fiberwiseIntervalEndpointPair_restriction]
  exact ⟨leftFibrations.comp_mem _ _
    (LeftFibration.mem (p := fiberwiseFunctorRestriction p arrowBoundaryι))
    (MorphismProperty.of_isIso _ (fiberwiseBoundaryIso p).hom)⟩

end SerrePositivity.InfinityCategories.F2
