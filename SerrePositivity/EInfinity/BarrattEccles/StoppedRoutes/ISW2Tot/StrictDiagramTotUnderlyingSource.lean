module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotalizationComparison
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotalizationInput
public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingDerivedComparison

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じstrict BE Tot頂点・図式・全評価に、実忘却Uの既存の全比較を適用する。
方針：既存algebraCAlgSource_underlyingDerivedIsoを同じ全nerveで前合成。
規約：IS-W2 R04の証明分割。加群Totへの最終比較やnative錐の同型の代用にしない。
使われ方：Totの全U比較の同じ両境界と元の台図式。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.ComplexLimits
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 同じBE Tot全頂点の実U像を、同じ元の計算複体の全像と比較する。 -/
def strictBETotUnderlyingSourceIso :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotVertex A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.cAlgForgetDerived A)
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory) ⋙
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A)) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) := by
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource_underlyingDerivedIso A).precomp
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory)))

/-- 同じstrict BE図式の実U像と、元の全台図式の導来像の全比較。 -/
def strictBECosimplicialUnderlyingDiagramIso
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialDiagram A F ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.cAlgForgetDerived A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialNerve A F ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.algebraUnderlyingDerivedSource A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource_underlyingDerivedIso A).precomp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialNerve A F)

/-- 元の全評価における実Uの比較は、同じ全評価で前合成した既存比較。 -/
def strictBECosimplicialUnderlyingEvaluationIso :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialEvaluation A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.cAlgForgetDerived A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialEvaluationNerve A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.algebraUnderlyingDerivedSource A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource_underlyingDerivedIso A).precomp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialEvaluationNerve A)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
