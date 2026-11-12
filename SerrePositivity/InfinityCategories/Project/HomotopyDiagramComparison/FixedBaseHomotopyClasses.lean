module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceTrivialFibration
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：自明 Kan fibration 上の円柱の類は、底の同じ raw な円柱によって一意に定まる。
方針：内部 Hom の自明 Kan 性と h Fun の忠実性を使い、底の円柱の一致を反映する。
規約：同じ両端だけでは比較しない。使われ方：終点固定比較と指定経路の作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 同じ底の raw 円柱を持つ二円柱は、自明 Kan fibration の上でも同じ辺の類を持つ。 -/
lemma trivialKanFibration_homotopy_homMk_eq {T E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    {a b : T ⟶ E} (H K : SSet.Homotopy a b) (h : H.h ≫ q = K.h ≫ q) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration ((ihom T).map q)
  apply hf.toHoFullyFaithful.map_injective
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
  congr 1
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv (curry (H.h ≫ q)) = SSet.yonedaEquiv (curry (K.h ≫ q))
  rw [h]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
