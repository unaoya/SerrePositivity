module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotVertexLocalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramLocalization

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じstrict BE余単体図式の台を、strict加群図式の∞局所化へ送る。
方針：指定AsSmall引き戻しと元のforgetを使い、objectwise擬同型を反転。
規約：IS-W2 R05のForgetStrictBEInfinity。同じΔ図式・全図式射を保持。
使われ方：局所化上のTotのU比較の右辺。BEの厳密化は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 元のAsSmall ΔのBE図式を、同じΔの台の複体図式として読む全関手。 -/
def strictBETotForgetDiagram :
    (AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) ⥤
      StrictComplexDiagram A .cosimplicial :=
  (Functor.whiskeringLeft SimplexCategory (AsSmall.{u} SimplexCategory)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj AsSmall.up ⋙
      (Functor.whiskeringRight SimplexCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
        (SerrePositivity.DifferentialGraded.Complex A)).obj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A))

/-- 台の図式への射は、元の同じ評価の複体射。 -/
theorem strictBETotForgetDiagram_map
    {F G : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : F ⟶ G)
    (j : SimplexCategory) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagram A).map f).app j = (f.app (AsSmall.up.obj j)).hom := rfl

/-- 元の全BE図式から、同じ加群図式の指定局所化への写像。 -/
def strictBETotForgetDiagramSource :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramNerve A ⟶ StrictDiagramInfinity A .cosimplicial :=
  nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagram A) ≫ strictDiagramLocalization A .cosimplicial

/-- 元のobjectwise擬同型は、台の同じ図式の局所化で可逆。 -/
theorem strictBETotForgetDiagramSource_inverts :
    InvertsEdges (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagramSource A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramWeakEdges A) := by
  intro s hs
  obtain ⟨F, G, f, rfl⟩ := ComposableArrows.mk₁_surjective s
  have h := strictDiagramLocalization_inverts A .cosimplicial
    (a := ComposableArrows.mk₁ ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagram A).map f))
    (show ComposableArrows.mk₁ ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagram A).map f) ∈
      strictDiagramWeakEdges A .cosimplicial from fun j => hs (AsSmall.up.obj j))
  change IsInvertibleEdge
    ((edgeOfSimplex (ComposableArrows.mk₁ ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagram A).map f))).map
      ((truncation 2).map (strictDiagramLocalization A .cosimplicial))) at h
  apply (isInvertibleEdge_congr
    (e := (edgeOfSimplex (ComposableArrows.mk₁ f)).map
      ((truncation 2).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagramSource A)))
    (f := (edgeOfSimplex (ComposableArrows.mk₁ ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagram A).map f))).map
      ((truncation 2).map (strictDiagramLocalization A .cosimplicial))) ?_).mpr h
  change (strictDiagramLocalization A .cosimplicial).app (Opposite.op ⦋1⦌)
    ((nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagram A)).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ f)) = _
  rw [nerveMap_app_mk₁]
  rfl

/-- 元のforget全関手の、指定BE局所化からの全延長の存在。 -/
theorem exists_strictBETotLocalizedForget :
    ∃ U : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A ⟶ StrictDiagramInfinity A .cosimplicial,
      Nonempty (FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization A ≫ U)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagramSource A)) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization_isLocalization A).exists_extension
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagramSource A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagramSource_inverts A)

/-- 同じstrict加群図式の局所化へ送る全forget比較。 -/
def strictBETotLocalizedForget :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A ⟶ StrictDiagramInfinity A .cosimplicial :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.exists_strictBETotLocalizedForget A).choose

/-- 局所化forgetの制限は元の全図式射のforgetと全同型で結ばれる。 -/
def strictBETotLocalizedForget_factor :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotLocalizedForget A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotForgetDiagramSource A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.exists_strictBETotLocalizedForget A).choose_spec.some

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
