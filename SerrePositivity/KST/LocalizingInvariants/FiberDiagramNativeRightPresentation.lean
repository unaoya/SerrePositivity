module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramNativeTriangleCommutation

/-!
概要：元の右辺比較を、標準二三角形と指定した BF 差の逆区間の合成として表示する。
方針：元の対角分解と上下の可換式を、BF 差の実合成三角形で貼り合わせる。
規約：元の全 h Fun 射の Arrow 等号を証明する。使われ方：fiber 頂点比較の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

lemma comp_of_invertible_triangle {C : Type*} [Category* C] {w x y z : C}
    (p : w ⟶ x) (a : x ⟶ y) (g : y ≅ z) (b : x ⟶ z) (r : w ⟶ z)
    (h : a ≫ g.hom = b) (k : p ≫ b = r) : p ≫ a = r ≫ g.inv := by
  apply (cancel_mono g.hom).mp
  simp only [Category.assoc, h, k, Iso.inv_hom_id, Category.comp_id]

namespace FiberDiagram

local instance nativeRightPresentationCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def nativeRightPresentation :=
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightCanonicalPost f)) ≫
  (SpectrumMappingPath.arrowIso (nativeRightMappingPath f)).inv ≫
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightCanonicalPre f))

lemma nativeRightLowerPost_upper :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightLowerPost f)) ≫
      SpectrumMappingPath.arrowHom (nativeRightUpperRealization f).path =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightCanonicalPost f)) ≫
      (SpectrumMappingPath.arrowIso (nativeRightMappingPath f)).inv := by
  exact comp_of_invertible_triangle _ _ (SpectrumMappingPath.arrowIso (nativeRightMappingPath f))
    _ _ (nativeRightArrowHom_comp f) (nativeRightLowerPost_comp f)

lemma rightRestriction_nativePresentation :
    Arrow.mk (rightRestriction.map f) = Arrow.mk (nativeRightPresentation f) := by
  rw [rightRestriction_decomposition]
  have hc := arrow_mk_comp_congr (rightAfterBottom_native f) (rightBeforeTop_native f)
  have hn : Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightLowerPost f)) ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightUpperPre f)) =
      nativeRightPresentation f := by
    rw [nativeRightUpperPre_eq, ← Category.assoc, nativeRightLowerPost_upper]
    exact Category.assoc _ _ _
  exact hc.trans (congrArg Arrow.mk hn)

end FiberDiagram
end SerrePositivity.KST.LocalizingInvariants
