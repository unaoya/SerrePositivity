module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionCanonicalNaturality
public import SerrePositivity.KST.LocalizingInvariants.FiberMappingPathLiftNaturality
public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementUnitNaturality

/-!
概要：PathLift と置換単位の比較式を、元の通常の合成三角形の全 h Fun 類で表示する。
方針：端点三角形の厳密な一致を、全ホモトピーの輸送と二つの可換式へ代入する。
規約：指定 γ と単位の全区間を保持。使われ方：模型の全右辺比較と元の表示の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants

local instance canonicalPrismCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

namespace FiberMapping.PathLift
variable {X Y Z : OmegaSpectrum.{u}} {p : Y ⟶ Z} {a : X ⟶ Y} {b : X ⟶ Z}
  {γ : (mappingSpace X Z).Edge (vertexOfHom (a ≫ p)) (vertexOfHom b)}
  (L : PathLift p a b γ)

lemma canonicalPost_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPost a p)) ≫
      SpectrumMappingPath.arrowHom γ =
    SpectrumMappingPath.arrowHom L.path ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (HomotopyArrow.rebase
        (SpectrumTriangleNormalization.canonicalPost L.map p) rfl
        (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge) L.fac))) := by
  simpa only [targetPost, SpectrumPostcomposition.sourcePost_canonical,
    SpectrumPostcomposition.targetPost_canonical] using L.post_naturality

lemma canonicalPre_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPre a p)) =
    SpectrumMappingPath.arrowHom γ ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (HomotopyArrow.rebase
        (SpectrumTriangleNormalization.canonicalPre L.map p)
        (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge) L.fac) rfl)) := by
  simpa only [targetPre, SpectrumPostcomposition.sourcePre_canonical,
    SpectrumPostcomposition.targetPre_canonical] using L.pre_naturality

end FiberMapping.PathLift
namespace FibrationReplacementComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

lemma canonicalUnitPost_naturality :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (HomotopyArrow.rebase
      (SpectrumTriangleNormalization.canonicalPost (fibrationReplacementUnit p ≫ map p q a b h)
        (fibrationReplacementProjection q)) rfl
      (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
        (unitFirst_projection p q a b h)))) =
    SpectrumMappingPath.arrowHom (unitPath p q a b h).path ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (HomotopyArrow.rebase
        (SpectrumTriangleNormalization.canonicalPost (a ≫ fibrationReplacementUnit q)
          (fibrationReplacementProjection q)) rfl
        (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
          (unitSecond_projection p q a b h)))) := by
  simpa only [unitSourcePost, unitTargetPost, SpectrumPostcomposition.sourcePost_canonical,
    SpectrumPostcomposition.targetPost_canonical] using unitPost_naturality p q a b h

lemma canonicalUnitPre_naturality :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (HomotopyArrow.rebase
      (SpectrumTriangleNormalization.canonicalPre (fibrationReplacementUnit p ≫ map p q a b h)
        (fibrationReplacementProjection q))
      (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
        (unitFirst_projection p q a b h)) rfl)) =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (HomotopyArrow.rebase
      (SpectrumTriangleNormalization.canonicalPre (a ≫ fibrationReplacementUnit q)
        (fibrationReplacementProjection q))
      (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
        (unitSecond_projection p q a b h)) rfl)) := by
  simpa only [unitSourcePre, unitTargetPre, SpectrumPostcomposition.sourcePre_canonical,
    SpectrumPostcomposition.targetPre_canonical] using unitPre_naturality p q a b h

end FibrationReplacementComparison
end SerrePositivity.KST.LocalizingInvariants
