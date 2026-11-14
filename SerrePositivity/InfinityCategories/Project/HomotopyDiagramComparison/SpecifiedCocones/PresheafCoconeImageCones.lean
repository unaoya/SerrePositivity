module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PresheafCoconeFlip
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits

/-!
概要：元の定義域全錐を指定前層余錐の交換評価で写し、底と余錐頂点の両像を回収する。
方針：元の全錐をそのまま写し、底制限と頂点評価を元の厳密な交換式で計算する。
規約：有限性・極限性を仮定せず、元の全錐・全脚・指定余錐を保持する。
使われ方：前層余極限頂点の実際の有限錐像を、元の全評価余錐の族と結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B C K : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C}
  (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) {p : K ⟶ C.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)

/-- 元の定義域全錐を、同じ元の指定余錐の全評価余錐の族へ写す。 -/
def presheafCoconeImageCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip q) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)

/-- 頂点評価による元の底図式は、元の指定余錐の頂点関手で写した図式そのもの。 -/
lemma presheafCoconeImageDiagram_apex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram ((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip q)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex ((SSet.uliftFunctor.{u + 1, u}).obj B)) =
        (SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip_apex]

/-- 同じ元の全錐の右頂点評価は、実際の余錐頂点関手で写した元の全錐そのもの。 -/
lemma presheafCoconeImageCone_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone (presheafCoconeImageCone q c)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex ((SSet.uliftFunctor.{u + 1, u}).obj B))).cast
        (presheafCoconeImageDiagram_apex q) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c) := by
  apply Subtype.ext
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip q) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip_apex]
  rfl

/-- 元の底制限図式は、同じ元の前層図式の交換評価で写した底図式。 -/
lemma presheafCoconeImageDiagram_restriction :
    ((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip q) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[0])).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =
        (SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _ r := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip_restriction]

/-- 元の全錐の底制限は、同じ元の前層図式の交換評価で写した元の全錐そのもの。 -/
lemma presheafCoconeImageCone_restriction :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[0])).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (presheafCoconeImageCone q c)).cast (presheafCoconeImageDiagram_restriction q) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _ r) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c) := by
  apply Subtype.ext
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip q) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeFlip_restriction]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
