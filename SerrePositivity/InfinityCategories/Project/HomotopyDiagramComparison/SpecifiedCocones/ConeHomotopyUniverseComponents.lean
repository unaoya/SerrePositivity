module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.ConeHomotopyUniverse
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FixedHomotopyEndpoints
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightTransportPostcomp

/-!
概要：同じ宇宙移送と係数の後合成で、全錐の変換の固定頂点と底の指定射を保つ。
方針：元の全ホモトピーの宇宙移送を同じ係数で写し、端点の表示は Arrow で扱う。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の任意の係数での極限の合成。
規約：元の全錐間の変換を保持し、点ごとの同型に置き換えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 同じ全錐のホモトピーを宇宙移送してから、同じ係数で後合成した射。 -/
def coneHomotopyUliftPostcompHom {K D : SSet.{u}} {p q : K ⟶ D}
    {c : JoinCone p} {d : JoinCone q} (H : SSet.Homotopy c.val d.val)
    {E : SSet.{max u v}} (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    FunctorHom (mapJoinCone U (JoinCone.ulift.{u, v} c)).val
      (mapJoinCone U (JoinCone.ulift.{u, v} d)).val :=
  SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (functorHomotopyPostcomp (coneHomotopyUlift.{u, v} H) U))

/-- 元の固定した頂点では、宇宙と係数を同じように移しても同じ全変換の成分は可逆。 -/
lemma coneHomotopyUliftPostcompHom_apex_isIso {K D : SSet.{u}} {p q : K ⟶ D}
    {c : JoinCone p} {d : JoinCone q} (H : SSet.Homotopy c.val d.val)
    (hH : (joinInl (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ joinInl (Δ[0] : SSet.{u}) K ≫ c.val)
    {E : SSet.{max u v}} (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    IsIso (functorHomEvaluate (coneHomotopyUliftPostcompHom H U)
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K)))) := by
  let i := joinInl (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K)
  let H' := functorHomotopyPostcomp (coneHomotopyUlift.{u, v} H) U
  have hH' : (i ▷ (Δ[1] : SSet.{max u v})) ≫ H'.h =
      fst (Δ[0] : SSet.{max u v}) (Δ[1] : SSet.{max u v}) ≫
        (i ≫ ((JoinCone.ulift.{u, v} c).val ≫ U)) := by
    change (i ▷ (Δ[1] : SSet.{max u v})) ≫ (coneHomotopyUlift.{u, v} H).h ≫ U = _
    rw [← Category.assoc, coneHomotopyUlift_fixedVertex H hH]
    simp only [i, Category.assoc]
  have hx : i.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{max u v}))) =
      SSet.yonedaEquiv i := by rw [← SSet.yonedaEquiv_comp, Category.id_comp]
  have h := functorHomEvaluate_isIso_of_fixedHomotopy_only H' i hH'
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{max u v})))
  rw [hx] at h
  exact h

/-- 底の元の指定余単位を同じ宇宙・係数へ移しても、全錐の変換の底と同じ射である。 -/
lemma coneHomotopyUliftPostcompHom_boundary_arrow {I K D : SSet.{u}}
    {δ : I ⟶ K} {F : K ⟶ D} {F₀ : I ⟶ D}
    {c : JoinCone (δ ≫ F)} {d : JoinCone F₀} (H : SSet.Homotopy c.val d.val)
    (α : SSet.Homotopy (δ ≫ F) F₀)
    (hH : (joinInr (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h = α.h)
    {E : SSet.{max u v}} (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    Arrow.mk ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{max u v})
      ((SSet.uliftFunctor.{v, u}).obj I))).app E)).toFunctor.map
        (coneHomotopyUliftPostcompHom H U)) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (kanRightCounitPostcomp (kanRightCounitUlift.{u, v} α) U))) := by
  unfold coneHomotopyUliftPostcompHom
  rw [← functorHomotopyPrecomp_hom]
  apply functorHomotopy_hom_arrow_of_h_eq
  change (joinInr (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj I) ▷
    (Δ[1] : SSet.{max u v})) ≫ (coneHomotopyUlift.{u, v} H).h ≫ U =
    simplexTensorMap.{v} α.h ≫ U
  rw [← Category.assoc, coneHomotopyUlift_boundary, hH]

/-- 宇宙と係数を移した元の制限錐の全射は、移した元の全錐の制限と同じ。 -/
lemma restrictJoinCone_ulift_postcomp_val {I K D : SSet.{u}} {p : K ⟶ D}
    (c : JoinCone p) (δ : I ⟶ K) {E : SSet.{max u v}}
    (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    (mapJoinCone U (JoinCone.ulift.{u, v} (restrictJoinCone c δ))).val =
      (restrictJoinCone (mapJoinCone U (JoinCone.ulift.{u, v} c))
        ((SSet.uliftFunctor.{v, u}).map δ)).val := by
  change (JoinCone.ulift.{u, v} (restrictJoinCone c δ)).val ≫ U =
    joinMap (𝟙 (Δ[0] : SSet.{max u v})) ((SSet.uliftFunctor.{v, u}).map δ) ≫
      ((JoinCone.ulift.{u, v} c).val ≫ U)
  rw [ulift_restrictJoinCone_val]
  change (joinMap (𝟙 (Δ[0] : SSet.{max u v})) ((SSet.uliftFunctor.{v, u}).map δ) ≫
    (JoinCone.ulift.{u, v} c).val) ≫ U = _
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
