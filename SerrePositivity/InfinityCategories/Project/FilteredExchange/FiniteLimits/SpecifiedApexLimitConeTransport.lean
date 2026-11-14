module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.ApexLimitConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：指定頂点円柱による極限錐の輸送を、全錐と制限の証拠とともに束ねる。
方針：証明済みの存在定理から同じ錐と全円柱を選ぶ。
規約：頂点の厳密な射と元の全図式を保持。使われ方：引き戻し比較の追跡可能な native 錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の極限錐から指定頂点へ輸送した錐と全円柱。
方針：構成済みの錐と境界制限を記録。規約：極限性を含めて構成する。使われ方：比較の公開。 -/
structure SpecifiedApexLimitConeTransport {K X : SSet.{u}} {p : K ⟶ X}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (a : (Δ[0] : SSet.{u}) ⟶ X)
    (P : (Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶ X) where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p
  isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cone
  apex_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ cone.val = a
  homotopy : SSet.Homotopy cone.val d.val
  boundary :
    (coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
      (β_ ((Δ[0] : SSet.{u}) ⨿ K) (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.apexConeBoundaryPrism p P
  vertical_isInvertible :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge homotopy x).toTruncated

/-- 概要：元の指定頂点円柱に沿う極限錐輸送を実際に構成する。
方針：同じ存在証明から錐と全比較円柱を同時に取る。
規約：図式と apex は指定どおり。使われ方：実際の Kan 比較による極限錐の頂点交換。 -/
def specifiedApexLimitConeTransport {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) (a : (Δ[0] : SSet.{u}) ⟶ X)
    (P : (Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[0] : SSet.{u}) ≫ P = a)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[0] : SSet.{u}) ≫ P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ d.val)
    (hP : ∀ x : (Δ[0] : SSet.{u}) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (P.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))) : SpecifiedApexLimitConeTransport d a P := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_limitCone_of_specifiedApexPrism d hd a P h₀ h₁ hP
  let c := Classical.choose h
  have hc := Classical.choose_spec h
  let G := Classical.choose hc.2.2
  have hG := Classical.choose_spec hc.2.2
  exact ⟨c, hc.1, hc.2.1, G, hG.1, hG.2⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
