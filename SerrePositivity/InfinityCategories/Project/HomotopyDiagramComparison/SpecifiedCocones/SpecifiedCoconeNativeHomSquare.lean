module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeEndHomotopies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorHomSquareRealization

/-!
概要：共通 end の元の二円柱と公開した native 比較を四辺に持つ実際の正方形。
方針：同じ raw な円柱の合成則を同じ型付き端点へ移し、関手単体集合で実現する。
規約：四辺の代表を固定。使われ方：共通 path end への全族の比較。
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
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y
local notation "IL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeIso hp p c hc dB hB dC y
local notation "IR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeIso hp p c hc dB dC hC y
local notation "NL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeHomotopy hp p c hc dB hB dC y
local notation "NR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeHomotopy hp p c hc dB dC hC y
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)

/-- 表示を揃えた元の HL・HR と同じ native 比較の積は、型付きの射として一致する。 -/
lemma specifiedCoconeNativeEndHom_comp : cls(L) ≫ (IL).hom = cls(R) ≫ (IR).hom := by
  have hL := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq L _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)
  have hR := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq R _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowComposition_congr hL rfl).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeHom_comp_hom_arrow hp p c hc dB hB dC hC y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowComposition_congr hR rfl).symm)
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 元の二円柱と公開した native 円柱を四辺に保つ全パラメータの正方形が存在する。 -/
lemma nonempty_specifiedCoconeNativeEndHomSquare : Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare L NR R NL) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonempty_functorHomSquare_of_homEq
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeHomotopy_hom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeHomotopy_hom]
  exact specifiedCoconeNativeEndHom_comp hp p c hc dB hB dC hC y

/-- 指定四辺を持つ、全 Hom のパラメータ上の実際の関手正方形。 -/
def specifiedCoconeNativeEndHomSquare : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare L NR R NL :=
  (nonempty_specifiedCoconeNativeEndHomSquare hp p c hc dB hB dC hC y).some

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
