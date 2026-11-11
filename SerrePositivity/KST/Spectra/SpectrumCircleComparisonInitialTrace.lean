module

public import SerrePositivity.KST.Spectra.CoherentTetrahedronInitialTrace
public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonCellObjects

/-!
概要：元の比較三単体の initial trace を、元の apex の BF 自己射の頂点へ厳密に戻す。
方針：元の apex 辺の等式を二つの面で読み、Hom の端点を移す。
規約：元の自己射を保持。使われ方：比較正方形の右辺を元の前合成として表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonInitialTraceSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の最初の辺の二面表示は、同じ元の BF 比較自己射の coherent 辺。 -/
lemma circleCompanionComparisonTetrahedron_apex_faces (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    Sp.δ 2 (Sp.δ 3 (circleCompanionComparisonTetrahedron z k)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleCompanionConeComparisonHom z)).edge := by
  erw [CoherentPathCoordinates.tetrahedronApex_yoneda,
    circleCompanionComparisonTetrahedron_apex, Equiv.apply_symm_apply]

/-- 元の initial trace は、端点を移すと元の BF 自己射の定値な Hom 頂点。 -/
lemma circleCompanionComparisonInitialTrace (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    CoherentPathCoordinates.tetrahedronInitialTrace (circleCompanionComparisonTetrahedron z k) ≫
      eqToHom (congrArg (fun s : Sp.{u} _⦋1⦌ ↦
        SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 1⟩))
          (circleCompanionComparisonTetrahedron_apex_faces z k)) =
      SSet.const (vertexOfHom (circleCompanionConeComparisonHom z)) := by
  rw [CoherentPathCoordinates.tetrahedronInitialTrace_of_apex
    (circleCompanionComparisonTetrahedron_apex_faces z k)]
  change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
    (SimplicialCategory.homEquiv' _ _ (circleCompanionConeComparisonHom z)) 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  congr 1
  change (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm
    (vertexOfHom (circleCompanionConeComparisonHom z))) = _
  exact Equiv.apply_symm_apply _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum
