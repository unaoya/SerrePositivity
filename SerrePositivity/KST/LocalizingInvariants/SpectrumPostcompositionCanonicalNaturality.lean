module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionEndpoints
public import SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleCommutation

/-!
概要：BF 後合成の自然性を、元の通常の合成三角形の前半・後半との等式にする。
方針：実 prism の端点の等号で、端点を正規化したホモトピー全体を同定する。
規約：全 h Fun 等号を保ち、追加の比較区間を選ばない。使われ方：模型の右辺表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumPostcomposition

local instance canonicalPostNaturalityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z) {f g : X ⟶ Y}
  (e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g))

lemma sourcePost_canonical : sourcePost p e = SpectrumTriangleNormalization.canonicalPost f p := by
  apply SSet.RelativeMorphism.Homotopy.ext
  change (HomotopyArrow.rebase _ _ _).h = _
  rw [HomotopyArrow.rebase_map]
  exact congrArg (fun k ↦ SquareDiagonal.postShape ≫ k) (sourceTriangle_eq p e)

lemma targetPost_canonical : targetPost p e = SpectrumTriangleNormalization.canonicalPost g p := by
  apply SSet.RelativeMorphism.Homotopy.ext
  change (HomotopyArrow.rebase _ _ _).h = _
  rw [HomotopyArrow.rebase_map]
  exact congrArg (fun k ↦ SquareDiagonal.postShape ≫ k) (targetTriangle_eq p e)

lemma sourcePre_canonical : sourcePre p e = SpectrumTriangleNormalization.canonicalPre f p := by
  apply SSet.RelativeMorphism.Homotopy.ext
  change (HomotopyArrow.rebase _ _ _).h = _
  rw [HomotopyArrow.rebase_map]
  exact congrArg (fun k ↦ SquareDiagonal.preShape ≫ k) (sourceTriangle_eq p e)

lemma targetPre_canonical : targetPre p e = SpectrumTriangleNormalization.canonicalPre g p := by
  apply SSet.RelativeMorphism.Homotopy.ext
  change (HomotopyArrow.rebase _ _ _).h = _
  rw [HomotopyArrow.rebase_map]
  exact congrArg (fun k ↦ SquareDiagonal.preShape ≫ k) (targetTriangle_eq p e)

lemma canonicalPost_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPost f p)) ≫
      SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge p e) =
    SpectrumMappingPath.arrowHom e ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPost g p)) := by
  simpa only [sourcePost_canonical, targetPost_canonical] using post_naturality p e

lemma canonicalPre_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPre f p)) =
    SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge p e) ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumTriangleNormalization.canonicalPre g p)) := by
  simpa only [sourcePre_canonical, targetPre_canonical] using pre_naturality p e

end SerrePositivity.KST.LocalizingInvariants.SpectrumPostcomposition
