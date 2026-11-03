module

public import SerrePositivity.InfinityCategories.Core.Idempotent.WeakShape
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLongEdge

/-!
概要：元の弱い retract の分裂点を固定して、元の全図式を右 fibration に持ち上げる。
方針：元の長辺の right anodyne 性を、元の Ret の pushout に沿って押し出す。
規約：指定した底の全弱図式と同じ分裂点を厳密に回収する。
使われ方：HTT 5.1.4.4 の slice 内の元の retract の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の弱い retract の分裂点の包含は right anodyne。 -/
lemma weakImagePoint_rightAnodyne : rightAnodyneExtensions weakImagePoint.{u} :=
  MorphismProperty.of_isPushout (IsPushout.of_hasPushout _ _).flip
    triangleLongEdge_rightAnodyne

/-- 指定した分裂点と元の底の全弱 retract 図式を厳密に保持する持ち上げが存在する。 -/
lemma weakDiagram_lift_exists {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p]
    (d : WeakRetractionDiagram Y) (x : (Δ[0] : SSet.{u}) ⟶ X)
    (h : x ≫ p = weakImagePoint.{u} ≫ d) :
    ∃ e : WeakRetractionDiagram X, weakImagePoint.{u} ≫ e = x ∧ e ≫ p = d := by
  have : HasLiftingProperty weakImagePoint.{u} p :=
    weakImagePoint_rightAnodyne p (RightFibration.mem (p := p))
  have sq : CommSq x weakImagePoint.{u} p d := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
