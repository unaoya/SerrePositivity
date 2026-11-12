module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitSpanHomEnd

/-!
概要：元の coherent 図式と部分余極限対象の span の固定終点余錐空間を実際の射で比較する。
方針：共通の左 Hom の end を通し、span 側の比較のホモトピー逆を選ぶ。
規約：余錐の普遍点の保存は別途必要。使われ方：余極限の貼り合わせの写像空間側の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB)
  (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)

/-- 共通の左 Hom の end から、実際の span の余錐空間へのホモトピー逆を選ぶ。 -/
def partialColimitSpanHomEndRetraction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomCospan hp p y c hc dB dC) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)) y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y).choose

/-- 選んだ逆も、実際の span の余錐空間へのホモトピー同値。 -/
lemma partialColimitSpanHomEndRetraction_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (partialColimitSpanHomEndRetraction hp p c hc dB dC y) := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd hp p c hc dB dC y, h.choose_spec.2, h.choose_spec.1⟩

/-- 元の固定終点余錐空間から、部分余極限頂点の実際の span の余錐空間への射。 -/
def partialColimitOriginalToSpanCocones :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)) y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC ≫
    partialColimitSpanHomEndRetraction hp p c hc dB dC y

/-- 境界の一方が単射なら、元の図式と部分余極限 span の余錐空間は実際にホモトピー同値。 -/
lemma partialColimitOriginalToSpanCocones_homotopyEquivalence [Mono g] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (partialColimitOriginalToSpanCocones hp p c hc dB hB dC hC y) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex _ _
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd_homotopyEquivalence hp p y c hc dB hB dC hC).comp
    (partialColimitSpanHomEndRetraction_homotopyEquivalence hp p c hc dB dC y)

/-- span への比較を共通 end へ戻すと、元の図式側の比較射と全単体でホモトピック。 -/
lemma partialColimitOriginalToSpanCocones_end_homotopy :
    Nonempty (SSet.Homotopy
      (partialColimitOriginalToSpanCocones hp p c hc dB hB dC hC y ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd hp p c hc dB dC y)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC)) := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y
  obtain ⟨H⟩ := h.choose_spec.2
  have hh := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC)
  simpa only [partialColimitOriginalToSpanCocones, partialColimitSpanHomEndRetraction,
    Category.assoc, Category.comp_id] using (show Nonempty (SSet.Homotopy _ _) from ⟨hh⟩)

/-- 同じ比較を、Kan 値図式の既存の native な coherent nerve の表示で公開する。 -/
def partialColimitOriginalToNativeSpanCocones :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)) y :=
  partialColimitOriginalToSpanCocones hp p c hc dB hB dC hC y ≫
    eqToHom (congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace t y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _))

/-- native な表示でも、元の図式と部分余極限 span の余錐空間の比較はホモトピー同値。 -/
lemma partialColimitOriginalToNativeSpanCocones_homotopyEquivalence [Mono g] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (partialColimitOriginalToNativeSpanCocones hp p c hc dB hB dC hC y) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex _ _
  exact (partialColimitOriginalToSpanCocones_homotopyEquivalence hp p c hc dB hB dC hC y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
