module

public import SerrePositivity.KST.Spectra.SpectrumMappingCompositionTransport
public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonInitialTrace

/-!
概要：元の比較 Hom 正方形の右辺は、元の companion 三角形への apex 射の前合成。
方針：四頂点の厳密等式と元の initial trace の頂点表示を豊穣合成へ代入する。
規約：元の BF 比較射と元の全 Hom を保持。使われ方：共通下辺の消去と符号計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonRightEdgesSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の右辺は、元の companion の三角形の trace による全 Hom の前合成。 -/
lemma circleCompanionComparisonRawHomSquare_includeFirst (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      circleCompanionComparisonRawHomSquare z k =
    CoherentPathCoordinates.triangleTrace (circleCompanionReflectedTriangle z k) ≫
      SpectrumMappingAcyclic.pre (circleCompanionConeComparisonHom z)
        (nativeCotensorInput PointedSimplicialSet.circle z).val := by
  let σ := circleCompanionComparisonTetrahedron z k
  let a := CoherentPathCoordinates.tetrahedronInitialTrace σ
  let b := CoherentPathCoordinates.triangleTrace (circleCompanionReflectedTriangle z k) ≫
    eqToHom (congrArg (fun s : Sp.{u} _⦋2⦌ ↦
      SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
        (circleCompanionComparisonTetrahedron_zero z k).symm)
  have ha : a ≫ eqToHom (congrArg₂ mappingSpace
      (circleCompanionComparisonTetrahedron_obj_zero z k)
      (circleCompanionComparisonTetrahedron_obj_one z k)) =
      SSet.const (vertexOfHom (circleCompanionConeComparisonHom z)) :=
    circleCompanionComparisonInitialTrace z k
  have hb : b ≫ eqToHom (congrArg₂ mappingSpace
      (circleCompanionComparisonTetrahedron_obj_one z k)
      (circleCompanionComparisonTetrahedron_obj_three z k)) =
      CoherentPathCoordinates.triangleTrace (circleCompanionReflectedTriangle z k) := by
    dsimp only [b]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have h := mappingComposition_transport
    (circleCompanionComparisonTetrahedron_obj_zero z k)
    (circleCompanionComparisonTetrahedron_obj_one z k)
    (circleCompanionComparisonTetrahedron_obj_three z k) a b
  rw [ha, hb] at h
  erw [mappingComposition_const_pre] at h
  rw [circleCompanionComparisonRawHomSquare, ← Category.assoc,
    circleCompanionComparisonHomSquare_includeFirst]
  simp only [Category.assoc, eqToHom_trans]
  exact h.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum
