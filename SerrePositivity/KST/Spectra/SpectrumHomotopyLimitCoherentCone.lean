module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitEndPoint
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedHomHolimComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConePointSection

/-!
概要：任意の小さい通常図式について、元の BF homotopy limit を頂点とする coherent な錐。
方針：恒等射の像の共通解像から得た反転 end の点を、γ3 の切断比較と固定頂点の全単射へ送る。
規約：実際の元の図式上の錐を構成する。極限性は後続の全 Hom パラメータの照合で示す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance coherentLimitConeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I]

/-- BF 恒等射の元の比較の像から得た、元の図式上の coherent な切断点。 -/
def homotopyLimitCoherentConePoint (D : I ⥤ OmegaSpectrum.{u}) :
    (coherentConeSectionSpace (strictCoherentDiagram D)
      (coherentNerveVertex (homotopyLimit D))) _⦋0⦌ :=
  (reflectedHomHolimConeComparison D (homotopyLimit D)).app _
    (ULift.up (homotopyLimitReflectedEndPoint D))

/-- 任意の小さい通常の BF 図式の、元の homotopy limit を頂点とする実際の coherent な錐。 -/
def homotopyLimitCoherentCone (D : I ⥤ OmegaSpectrum.{u}) :
    JoinCone (strictCoherentDiagram D) :=
  ((fixedVertexConeSpaceEquiv (strictCoherentDiagram D)
    (coherentNerveVertex (homotopyLimit D))).symm (homotopyLimitCoherentConePoint D)).val

/-- 構成した錐の頂点は、元の BF homotopy limit の頂点そのもの。 -/
lemma homotopyLimitCoherentCone_vertex (D : I ⥤ OmegaSpectrum.{u}) :
    (homotopyLimitCoherentCone D).vertex = coherentNerveVertex (homotopyLimit D) := by
  have h := ((fixedVertexConeSpaceEquiv (strictCoherentDiagram D)
    (coherentNerveVertex (homotopyLimit D))).symm (homotopyLimitCoherentConePoint D)).property
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] _ ≫ (homotopyLimitCoherentCone D).val) = _
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 構成した錐の正規化した coslice 切断は、元の反転 end の点から得た切断の評価。 -/
lemma homotopyLimitCoherentCone_cosliceSection (D : I ⥤ OmegaSpectrum.{u}) :
    coherentConeCosliceSection (homotopyLimitCoherentCone D) ≫
        eqToHom (congrArg (fun w ↦ sliceUnder (SSet.yonedaEquiv.symm w))
          (homotopyLimitCoherentCone_vertex D)) =
      inv (CartesianMonoidalCategory.fst _ (Δ[0] : SSet.{u + 1})) ≫
        relativeFunctorUncurry (SSet.yonedaEquiv.symm (homotopyLimitCoherentConePoint D)) :=
  fixedVertexConeSpaceEquiv_cosliceSection (strictCoherentDiagram D)
    (coherentNerveVertex (homotopyLimit D)) (homotopyLimitCoherentConePoint D)
    (homotopyLimitCoherentCone_vertex D)

end SerrePositivity.KST.Spectra.OmegaSpectrum
