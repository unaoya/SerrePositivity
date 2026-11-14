module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationComparison
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationInput
public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingDerivedComparison

/-!
概要：同じstrict BE Tot頂点・図式・全評価に、実忘却Uの既存の全比較を適用する。
方針：既存algebraCAlgSource_underlyingDerivedIsoを同じ全nerveで前合成。
規約：IS-W2 R04の証明分割。加群Totへの最終比較やnative錐の同型の代用にしない。
使われ方：Totの全U比較の同じ両境界と元の台図式。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じBE Tot全頂点の実U像を、同じ元の計算複体の全像と比較する。 -/
def strictBETotUnderlyingSourceIso :
    FunctorIso (strictBETotVertex A ≫ cAlgForgetDerived A)
      (nerveMap (framedLimitFunctor A (AsSmall.{u} SimplexCategory) ⋙
        Operad.Algebra.forget (operad A)) ≫ complexOrdinaryDerivedSource A) := by
  exact (algebraCAlgSource_underlyingDerivedIso A).precomp
    (nerveMap (framedLimitFunctor A (AsSmall.{u} SimplexCategory)))

/-- 同じstrict BE図式の実U像と、元の全台図式の導来像の全比較。 -/
def strictBECosimplicialUnderlyingDiagramIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    FunctorIso (strictBECosimplicialDiagram A F ≫ cAlgForgetDerived A)
      (strictBECosimplicialNerve A F ≫ algebraUnderlyingDerivedSource A) :=
  (algebraCAlgSource_underlyingDerivedIso A).precomp (strictBECosimplicialNerve A F)

/-- 元の全評価における実Uの比較は、同じ全評価で前合成した既存比較。 -/
def strictBECosimplicialUnderlyingEvaluationIso :
    FunctorIso (strictBECosimplicialEvaluation A ≫ cAlgForgetDerived A)
      (strictBECosimplicialEvaluationNerve A ≫ algebraUnderlyingDerivedSource A) :=
  (algebraCAlgSource_underlyingDerivedIso A).precomp (strictBECosimplicialEvaluationNerve A)

end SerrePositivity.EInfinity.BarrattEccles
