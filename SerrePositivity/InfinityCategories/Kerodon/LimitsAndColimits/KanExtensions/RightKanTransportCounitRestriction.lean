module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalHomRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportDiagramHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.UniversalProperty
public import Mathlib.CategoryTheory.HomCongr

/-!
概要：元の大域比較の指定余単位との両立を、同じ右Kan輸送の図式側で評価する。
方針：同じ標準形状の前合成と係数移送の合成則を使い、元のhom_facをそのまま適用する。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の計算法則。
使われ方：S8 の大域比較の成分を、指定された同じ極限頂点比較に照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元のhom_facを、標準錐による前合成と指定輸送の同じ図式側で評価する。 -/
lemma rightKanTransport_counit_restriction
    {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (η : FunctorHom F G)
    (hη : rightKanHomMap δ (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy β)) F η =
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
    (c : C _⦋0⦌) (t : RightKanConeTransport δ F₀ G β c) :
    let ηq : FunctorHom (rightKanCanonicalCone δ F c).val (rightKanCanonicalCone δ G c).val :=
      (hoFunctor.map ((pre (rightKanCanonicalShape δ c)).app D)).toFunctor.map η
    kanFunctorHomCongr (rightKanCanonicalCone δ F c).property t.cone.property
      ((hoFunctor.map (coneRestriction (rightKanShape δ c) D)).toFunctor.map
        (ηq ≫ Truncated.HomotopyCategory.homMk t.edge)) =
      (hoFunctor.map ((pre (rightKanProjection δ c)).app D)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)) := by
  dsimp only
  rw [Functor.map_comp]
  have hc : ∀ (a : FunctorHom
      (joinInr Δ[0] (rightKanShape δ c) ≫ (rightKanCanonicalCone δ F c).val)
      (joinInr Δ[0] (rightKanShape δ c) ≫ (rightKanCanonicalCone δ G c).val))
      (b : FunctorHom
        (joinInr Δ[0] (rightKanShape δ c) ≫ (rightKanCanonicalCone δ G c).val)
        (joinInr Δ[0] (rightKanShape δ c) ≫ t.cone.val)),
      kanFunctorHomCongr (rightKanCanonicalCone δ F c).property t.cone.property (a ≫ b) =
        kanFunctorHomCongr (rightKanCanonicalCone δ F c).property
          (rightKanCanonicalCone δ G c).property a ≫
        kanFunctorHomCongr (rightKanCanonicalCone δ G c).property t.cone.property b := by
    intro a b
    exact Iso.homCongr_comp _ _ _ a b
  rw [hc]
  have hq := rightKanCanonicalShape_hom_restriction δ c η
  change kanFunctorHomCongr (rightKanCanonicalCone δ F c).property
      (rightKanCanonicalCone δ G c).property _ = _ at hq
  have hs := t.diagram_hom
  dsimp only [coneRestriction] at hs ⊢
  rw [hq, hs, ← Functor.map_comp]
  exact congrArg ((hoFunctor.map ((pre (rightKanProjection δ c)).app D)).toFunctor.map) hη

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
