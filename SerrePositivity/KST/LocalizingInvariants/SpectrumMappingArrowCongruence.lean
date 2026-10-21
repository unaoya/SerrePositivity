module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionNaturality
public import SerrePositivity.KST.LocalizingInvariants.HomotopyMapTransport

/-!
概要：同じ BF 区間の全一単体を持つ端点輸送は、同じ全 h Fun 比較を与える。
方針：全辺族の射の合同性をホモトピーの合同性と辺の像の同定へ渡す。
規約：端点も Arrow の等号で保持。使われ方：置換前後の指定 γ の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath

variable {X Y : OmegaSpectrum.{u}} {f₀ g₀ f₁ g₁ : X ⟶ Y}
  (e₀ : (mappingSpace X Y).Edge (vertexOfHom f₀) (vertexOfHom g₀))
  (e₁ : (mappingSpace X Y).Edge (vertexOfHom f₁) (vertexOfHom g₁))

lemma arrowHom_congr (h : e₀.edge = e₁.edge) :
    Arrow.mk (arrowHom e₀) = Arrow.mk (arrowHom e₁) := by
  have hm := homotopy_map_congr e₀ e₁ h
  have ha := HomotopyArrow.congr (homotopy e₀) (homotopy e₁) hm
  exact (SpectrumPostcomposition.path_arrow e₀).symm.trans
    (ha.trans (SpectrumPostcomposition.path_arrow e₁))

lemma arrowHom_ofHomEq (h₀ : f₀ = f₁) (h₁ : g₀ = g₁) :
    Arrow.mk (arrowHom e₀) = Arrow.mk (arrowHom
      (e₀.ofEq (congrArg vertexOfHom h₀) (congrArg vertexOfHom h₁))) := by
  subst f₁ g₁
  rfl

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
