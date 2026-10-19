module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKReflectedPoints
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedHomHolimComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConePointSection

/-!
概要：元の円 cotensor の恒等射の像から、固定図式上の実際の coherent な錐を構成する。
方針：反転 BK 切断点を共有の切断比較へ送り、頂点を固定した錐の全単射で戻す。
規約：頂点は元の cotensor。使われ方：この具体的な錐全体の族を用いる ∞ 極限性の証明。
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
local instance circleCoherentConeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の反転 BK 切断点の射が表す、同じ end の実際の零単体。 -/
def circleBKReflectedEndPoint (Y : OmegaSpectrum.{u}) :
    (bousfieldKanHolim (simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor)) _⦋0⦌ :=
  SSet.unitHomEquiv _ (circleBKReflectedEndPointMap Y)

/-- 元の反転 BK 切断点の、固定図式全体上の coherent な切断点。 -/
def circleBKCoherentConePoint (Y : OmegaSpectrum.{u}) :
    (coherentConeSectionSpace (strictCoherentDiagram (pointLoopDiagram Y))
      (coherentNerveVertex (cotensor PointedSimplicialSet.circle Y))) _⦋0⦌ :=
  (reflectedHomHolimConeComparison (pointLoopDiagram Y)
    (cotensor PointedSimplicialSet.circle Y)).app _ (ULift.up (circleBKReflectedEndPoint Y))

/-- 元の円評価の BK 切断点が与える、元の cotensor を頂点とする実際の coherent な錐。 -/
def circleBKCoherentCone (Y : OmegaSpectrum.{u}) :
    JoinCone (strictCoherentDiagram (pointLoopDiagram Y)) :=
  ((fixedVertexConeSpaceEquiv (strictCoherentDiagram (pointLoopDiagram Y))
    (coherentNerveVertex (cotensor PointedSimplicialSet.circle Y))).symm
      (circleBKCoherentConePoint Y)).val

/-- この錐の頂点は、元の円 cotensor の標準頂点に厳密一致する。 -/
lemma circleBKCoherentCone_vertex (Y : OmegaSpectrum.{u}) :
    (circleBKCoherentCone Y).vertex =
      coherentNerveVertex (cotensor PointedSimplicialSet.circle Y) := by
  have h := ((fixedVertexConeSpaceEquiv (strictCoherentDiagram (pointLoopDiagram Y))
    (coherentNerveVertex (cotensor PointedSimplicialSet.circle Y))).symm
      (circleBKCoherentConePoint Y)).property
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] _ ≫ (circleBKCoherentCone Y).val) = _
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 構成した錐の正規化した coslice 切断は、元の反転切断点の評価そのもの。 -/
lemma circleBKCoherentCone_cosliceSection (Y : OmegaSpectrum.{u}) :
    coherentConeCosliceSection (circleBKCoherentCone Y) ≫
        eqToHom (congrArg (fun w ↦ sliceUnder (SSet.yonedaEquiv.symm w))
          (circleBKCoherentCone_vertex Y)) =
      inv (CartesianMonoidalCategory.fst _ (Δ[0] : SSet.{u + 1})) ≫
        relativeFunctorUncurry (SSet.yonedaEquiv.symm (circleBKCoherentConePoint Y)) :=
  fixedVertexConeSpaceEquiv_cosliceSection (strictCoherentDiagram (pointLoopDiagram Y))
    (coherentNerveVertex (cotensor PointedSimplicialSet.circle Y)) (circleBKCoherentConePoint Y)
    (circleBKCoherentCone_vertex Y)

end SerrePositivity.KST.Spectra.OmegaSpectrum
