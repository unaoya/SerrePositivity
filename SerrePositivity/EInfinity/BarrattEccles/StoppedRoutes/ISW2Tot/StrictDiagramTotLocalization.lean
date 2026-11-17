module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotalizationInput
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneralLocalization

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のstrict BE余単体図式を、同じobjectwise擬同型で局所化する。
方針：既存edgeLocalizationを元の通常nerveの指定辺集合に適用。
規約：IS-W2 R05の証明分割。任意coherent BE図式の厳密化は主張しない。
使われ方：同じ全評価・Tot頂点・U比較の局所化への輸送の源。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 元のstrict BE余単体図式の全通常nerve。 -/
abbrev StrictBETotDiagramNerve : SSet.{u+1} :=
  nerve (AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)

/-- 元の全自然変換の各成分が擬同型である、指定辺の集合。 -/
def strictBETotDiagramWeakEdges : Set ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramNerve A) _⦋1⦌) :=
  {s | ∀ j, QuasiIso ((s.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).app j).hom}

/-- 一辺の指定条件は元の同じ全成分の擬同型性。 -/
theorem strictBETotDiagramWeakEdges_mk₁
    {F G : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : F ⟶ G) :
    ComposableArrows.mk₁ f ∈ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramWeakEdges A ↔
      ∀ j, QuasiIso (f.app j).hom := Iff.rfl

/-- 元のstrict BE図式の指定objectwise擬同型の∞局所化。 -/
def StrictBETotDiagramInfinity : SSet.{u+1} :=
  edgeLocalization (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramNerve A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramWeakEdges A)

instance strictBETotDiagramInfinity_quasicategory :
    Quasicategory (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A) := edgeLocalization_quasicategory _ _

/-- 元の全strict図式のnerveからの指定局所化写像。 -/
def strictBETotDiagramLocalization :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramNerve A ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotDiagramInfinity A := edgeLocalizationMap _ _

/-- 同じ指定写像の全関手圏の普遍性。 -/
theorem strictBETotDiagramLocalization_isLocalization :
    IsLocalization (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramLocalization A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotDiagramWeakEdges A) :=
  edgeLocalization_isLocalization _ _

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
