module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeAttachmentOriginalCoherence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorHomSquareRealization

/-!
概要：元の HL・HR と枝比較・根辺比較・付加辺面比較を四辺に持つ実際の正方形。
方針：同じ型付き端点での合成の等式を、同じ四つの円柱を保って実現する。
規約：四辺の代表を固定。使われ方：共通 path end 内の実際の全族の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB)
  (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)

section
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y
local notation "B₁" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchLegHomotopy hp p c hc dB hB dC y
local notation "C₁" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftHomCylinderComparison hp p c hc dB dC y
local notation "D₁" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentHomotopy hp p c hc dB dC y
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)

/-- 元の左の四円柱の合成則は、同じ型付き端点の射として成立する。 -/
lemma specifiedCoconeLeftAttachment_original_homMk_comp : cls(L) ≫ cls(B₁) = cls(C₁) ≫ cls(D₁) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachment_original_homMk_comp_arrow hp p c hc dB hB dC y
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 元の左 HL・HR を下辺、枝比較を右辺、根辺比較を左辺、付加辺面比較を上辺に保つ。 -/
def specifiedCoconeLeftAttachmentOriginalSquare : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare L D₁ C₁ B₁ :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonempty_functorHomSquare_of_homEq L D₁ C₁ B₁
    (specifiedCoconeLeftAttachment_original_homMk_comp hp p c hc dB hB dC y)).some
end

section
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y
local notation "B₁" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchLegHomotopy hp p c hc dB dC hC y
local notation "C₁" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y
local notation "D₁" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentHomotopy hp p c hc dB dC y
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)

/-- 元の右の四円柱の合成則は、同じ型付き端点の射として成立する。 -/
lemma specifiedCoconeRightAttachment_original_homMk_comp :
    cls(L) ≫ cls(B₁) = cls(C₁) ≫ cls(D₁) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachment_original_homMk_comp_arrow hp p c hc dB dC hC y
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 元の右 HL・HR を下辺、枝比較を右辺、根辺比較を左辺、付加辺面比較を上辺に保つ。 -/
def specifiedCoconeRightAttachmentOriginalSquare : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare L D₁ C₁ B₁ :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonempty_functorHomSquare_of_homEq L D₁ C₁ B₁
    (specifiedCoconeRightAttachment_original_homMk_comp hp p c hc dB dC hC y)).some
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
