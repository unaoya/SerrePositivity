module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomInitiality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PartialColimitHomEnd
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PartialColimitSpecifiedPathCocone

/-!
概要：貼った余錐の余極限性を、共通の左 Hom の end への全 Hom の族の同値性へ正確に帰着する。
方針：既存の余錐空間から end への実際の同値を消去し、点の Hom の始対象性判定を適用する。
規約：end 比較の同値性は結論せず、残る検証条件として明示。使われ方：指定経路で構成した余錐の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D X : SSet.{u}} [Quasicategory X] {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB)
  (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC)

/-- 任意の元の余錐の全 Hom の族を、部分余極限頂点の共通 end へ写す実際の射。 -/
def partialColimitHomFamilyToEnd (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft d.vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomCospan hp p y c hc dB dC) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC

/-- 元の余錐の余極限性は、共通 end への全 Hom の族が全終点で同値となることと同値。 -/
lemma isColimitCone_iff_partialColimitHomFamilyToEnd [Mono g] (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ↔ ∀ y : X _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (partialColimitHomFamilyToEnd hp p c hc dB hB dC hC d y) := by
  constructor
  · intro hd y
    have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex p y
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily_homotopyEquivalence d hd y).comp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd_homotopyEquivalence hp p y c hc dB hB dC hC)
  · intro h
    let H := fun y ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomCospan hp p y c hc dB dC)
    let (y : X _⦋0⦌) : KanComplex (H y) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedSections_kanComplex _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_pointHomFamily_comparison d H
      (fun y ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC)
      (fun y ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeToHomEnd_homotopyEquivalence hp p y c hc dB hB dC hC) h

/-- 同じ全 Hom の族を、ホモトピー逆を選ぶ前の共通 path end へ写す射。 -/
def partialColimitHomFamilyToPathEnd (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft d.vertex y ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomPathEnd hp p y c hc dB dC :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeHomEndComparison hp p y c hc dB hB dC hC

/-- 共通 path end への全 Hom の族の同値性も、元の余錐の余極限性の必要十分条件。 -/
lemma isColimitCone_iff_partialColimitHomFamilyToPathEnd [Mono g] (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ↔ ∀ y : X _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (partialColimitHomFamilyToPathEnd hp p c hc dB hB dC hC d y) := by
  constructor
  · intro hd y
    have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex p y
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily_homotopyEquivalence d hd y).comp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeHomEndComparison_homotopyEquivalence hp p y c hc dB hB dC hC)
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_pointHomFamily_comparison d
      (fun y ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomPathEnd hp p y c hc dB dC)
      (fun y ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeHomEndComparison hp p y c hc dB hB dC hC)
      (fun y ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitCoconeHomEndComparison_homotopyEquivalence hp p y c hc dB hB dC hC) h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
