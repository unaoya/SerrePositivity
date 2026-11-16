module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCocartesian
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：同じ指定右Kan輸送の図式側の辺は、元の指定余単位の制限の類を表す。
方針：輸送のdiagramをcurryし、既存の前合成の類と端点の係数移送を照合する。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存輸送の計算法則。
使われ方：S8 の元の大域比較のhom_facを、同じ比較錐の輸送の基底で評価する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元の輸送の図式側の射の類を、同じ指定余単位の前合成として表示する。 -/
lemma RightKanConeTransport.diagram_hom
    {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) :
    kanFunctorHomCongr (rightKanCanonicalCone δ F c).property t.cone.property
      ((hoFunctor.map (coneRestriction (rightKanShape δ c) D)).toFunctor.map
        (Truncated.HomotopyCategory.homMk t.edge)) =
      (hoFunctor.map ((pre (rightKanProjection δ c)).app D)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)) := by
  let γ := functorHomotopyPrecomp α (rightKanProjection δ c)
  have he : (t.edge.map ((truncation 2).map (coneRestriction (rightKanShape δ c) D))).edge =
      (functorEdgeOfSimplicialHomotopy γ).edge := by
    change SSet.yonedaEquiv (curry t.family ≫
        (pre (joinInr Δ[0] (rightKanShape δ c))).app D) =
      SSet.yonedaEquiv (curry ((rightKanProjection δ c ▷ Δ[1]) ≫ α.h))
    congr 1
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry, t.diagram]
  have h := homMk_transport
    (congrArg functorVertex (rightKanCanonicalCone δ F c).property)
    (congrArg functorVertex t.cone.property)
    (t.edge.map ((truncation 2).map (coneRestriction (rightKanShape δ c) D)))
    (functorEdgeOfSimplicialHomotopy γ) he
  simpa only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    γ, functorHomotopyPrecomp_hom, Category.assoc, SSet.hoFunctor,
    Functor.toCatHom_toFunctor, SSet.mapHomotopyCategory,
    Truncated.mapHomotopyCategory_homMk] using h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
