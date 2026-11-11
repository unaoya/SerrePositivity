module

public import SerrePositivity.KST.LocalizingInvariants.CompositionIdentityShape
public import SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleCommutation

/-!
概要：恒等 BF 射を含む標準三角形の辺比較を、全 h Fun の恒等射と同定する。
方針：通常の nerve の退化を coherent nerve へ移し、退化格子の射影を計算する。
規約：端点輸送を Arrow の等号で保持。使われ方：模型の置換単位の表示の簡約。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization

local instance identityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {A B : OmegaSpectrum.{u}} (a : A ⟶ B)

lemma canonical_right_identity : canonical a (𝟙 B) =
    (SimplicialNerve OmegaSpectrum).σ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum).app (Opposite.op ⦋2⦌) (ComposableArrows.mk₂ a (𝟙 B)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, ← σ_naturality_apply]
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum).app (Opposite.op ⦋2⦌))
  exact ComposableArrows.ext₂ rfl rfl rfl (by simp; rfl) (by simp; rfl)

lemma canonical_left_identity : canonical (𝟙 A) a =
    (SimplicialNerve OmegaSpectrum).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum).app (Opposite.op ⦋2⦌) (ComposableArrows.mk₂ (𝟙 A) a) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, ← σ_naturality_apply]
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum).app (Opposite.op ⦋2⦌))
  exact ComposableArrows.ext₂ rfl rfl rfl (by simp; rfl) (by simp; rfl)

lemma canonicalPost_identity_map : (canonicalPost a (𝟙 B)).h =
    fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge := by
  change SquareDiagonal.postShape ≫ SSet.yonedaEquiv.symm (canonical a (𝟙 B)) = _
  rw [canonical_right_identity]
  have he : SSet.yonedaEquiv.symm ((SimplicialNerve OmegaSpectrum).σ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge) =
      stdSimplex.σ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_σ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [he, ← Category.assoc, CompositionIdentity.post_degenerate]

lemma canonicalPre_identity_map : (canonicalPre (𝟙 A) a).h =
    fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge := by
  change SquareDiagonal.preShape ≫ SSet.yonedaEquiv.symm (canonical (𝟙 A) a) = _
  rw [canonical_left_identity]
  have he : SSet.yonedaEquiv.symm ((SimplicialNerve OmegaSpectrum).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge) =
      stdSimplex.σ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_σ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [he, ← Category.assoc, CompositionIdentity.pre_degenerate]

lemma canonicalPost_identity_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPost a (𝟙 B)))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge)))) :=
  HomotopyArrow.identity _ _ (canonicalPost_identity_map a)

lemma canonicalPre_identity_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre (𝟙 A) a))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge)))) :=
  HomotopyArrow.identity _ _ (canonicalPre_identity_map a)

end SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization
