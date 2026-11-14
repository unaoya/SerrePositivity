module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.StrictSpanPointHomEnd
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.SpanPointHomEndInverseHomotopies

/-!
概要：strict な native span の元の点 Hom end 比較を、同じ辺全族の end へ戻す。
方針：同じ horn 表示の制限を元の逆の余単位円柱に前合成する。
規約：元の strict 比較と任意の元の全族を保持。使われ方：native な普遍族の経路の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {X : SSet.{max u v}} [Quasicategory X]
  (p : (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} WalkingSpan)) ⟶ X) (y : X _⦋0⦌)
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p (Iso.inv _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanHornIso) y
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanHornDiagram p

/-- 元の strict span の点 Hom 比較を戻すと、同じ horn 制限からの辺全族比較へ至る。 -/
def strictSpanPointHomEndReturn : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanCoconeToPointHomEnd p y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanPointHomToEdgeEnd q y)
    (r ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconeToEdgeEnd q y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconePointHomEndReturn q y) r)
    (Category.assoc _ _ _).symm rfl

/-- strict 表示の戻しも、元の同じ horn 制限を元の余単位円柱に前合成した射。 -/
lemma strictSpanPointHomEndReturn_raw :
    (strictSpanPointHomEndReturn p y).h =
      (r ▷ (Δ[1] : SSet.{max u v})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconePointHomEndReturn q y).h := rfl

/-- 任意の同じ全族の点 Hom end 比較も、同じパラメータで辺全族 end へ戻せる。 -/
def strictSpanPointHomEndFamilyReturn {T : SSet.{max u v}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) : SSet.Homotopy
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictSpanCoconeToPointHomEnd p y) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanPointHomToEdgeEnd q y)
    (a ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconeToEdgeEnd q y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (strictSpanPointHomEndReturn p y) a)
    (Category.assoc _ _ _).symm rfl

/-- 全族の戻しは、同じ元の全族を同じ strict 戻し円柱に前合成した raw な射。 -/
lemma strictSpanPointHomEndFamilyReturn_raw {T : SSet.{max u v}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) :
    (strictSpanPointHomEndFamilyReturn p y a).h =
      (a ▷ (Δ[1] : SSet.{max u v})) ≫ (strictSpanPointHomEndReturn p y).h := rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
