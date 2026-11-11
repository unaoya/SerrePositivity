module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomFamilyInitiality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomFamily

/-!
概要：任意の余錐の全 Hom の族の同値性を、実際の余極限性の必要十分条件にする。
方針：余錐圏の left fibration に点の始対象性の反映を適用し、共通模型への同値を消去する。
規約：比較対象に Kan 性を明示する。使われ方：共通 end の全 Hom の比較から貼った余錐の普遍性を結論。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)

/-- 任意の余錐の余極限性は、その全 Hom による余錐空間の族の実際のホモトピー同値性と同値。 -/
lemma isColimitCone_iff_coconePointHomFamily_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ↔ ∀ y : X _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isInitialVertex_iff_pointHomFamily_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) d

/-- 余錐空間の共通 Kan 模型への比較が同値なら、全 Hom の族の合成の同値性から余極限性を反映。 -/
lemma isColimitCone_of_pointHomFamily_comparison
    (H : X _⦋0⦌ → SSet.{u}) [∀ y, KanComplex (H y)]
    (q : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y ⟶ H y)
    (hq : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (q y))
    (h : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y ≫ q y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  apply (isColimitCone_iff_coconePointHomFamily_homotopyEquivalence d).mpr
  intro y
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex p y
  have he := (hq y).isQCatEquivalence.cancel_right (h y).isQCatEquivalence
  exact he.isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
