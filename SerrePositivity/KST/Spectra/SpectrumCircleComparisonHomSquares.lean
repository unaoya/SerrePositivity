module

public import SerrePositivity.KST.Spectra.SpectrumCircleConeComparisonCells
public import SerrePositivity.KST.Spectra.CoherentSimplexCompositionFaces

/-!
概要：元の錐の比較の左右の Hom 正方形を同じ Hom に表示し、その四辺を計算する。
方針：共通の二面で端点を移送し、実際の三単体の四つの面の trace の式を適用する。
規約：全ての端点の等式を保持。使われ方：共通の中央経路の消去による apex 射の符号判定。
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
local instance circleComparisonHomSquaresSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の中央三角形の始点・終点の同じ Hom。左右の比較正方形で共通に使う。 -/
abbrev circleComparisonCentralHom (z : Sp.{u} _⦋0⦌) : SSet.{u} :=
  SimplicialCategory.sHom ((circleCompanionComparisonCentralTriangle z).obj ⟨ULift.up 0⟩)
    ((circleCompanionComparisonCentralTriangle z).obj ⟨ULift.up 2⟩)

/-- 元の錐の比較の三単体の Hom 正方形を、元の共通の中央三角形の Hom に移送する。 -/
def circleCompanionComparisonHomSquare (z : Sp.{u} _⦋0⦌) (k : Limits.WalkingPair) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ circleComparisonCentralHom z :=
  CoherentPathCoordinates.tetrahedronTraceAgainst
    (circleCompanionComparisonTetrahedron_two z k)

/-- 元の評価錐の三角形の Hom も、同じ元の中央三角形の Hom に移送できる。 -/
lemma circleNativeComparisonTriangle_hom (z : Sp.{u} _⦋0⦌) (k : Limits.WalkingPair) :
    SimplicialCategory.sHom ((circleNativeComparisonTriangle z k).obj ⟨ULift.up 0⟩)
      ((circleNativeComparisonTriangle z k).obj ⟨ULift.up 2⟩) = circleComparisonCentralHom z := by
  have h1 := congrArg (fun s : (SimplicialNerve OmegaSpectrum.{u}) _⦋2⦌ ↦
    SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
    (circleCompanionComparisonTetrahedron_one z k)
  have h2 := congrArg (fun s : (SimplicialNerve OmegaSpectrum.{u}) _⦋2⦌ ↦
    SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
    (circleCompanionComparisonTetrahedron_two z k)
  exact h1.symm.trans h2

/-- 正方形の左辺は、元の評価錐の同じ三角形の trace。 -/
lemma circleCompanionComparisonHomSquare_skipFirst (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      circleCompanionComparisonHomSquare z k =
    CoherentPathCoordinates.triangleTrace (circleNativeComparisonTriangle z k) ≫
      eqToHom (circleNativeComparisonTriangle_hom z k) := by
  rw [circleCompanionComparisonHomSquare, CoherentPathCoordinates.tetrahedronTraceAgainst,
    ← Category.assoc, CoherentPathCoordinates.tetrahedronTrace_skipFirst]
  exact CoherentPathCoordinates.triangleTrace_transport
    (circleCompanionComparisonTetrahedron_one z k) _ _

/-- 正方形の下辺は、左右で同じ元の中央三角形の trace。 -/
lemma circleCompanionComparisonHomSquare_skipSecond (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      circleCompanionComparisonHomSquare z k =
    CoherentPathCoordinates.triangleTrace (circleCompanionComparisonCentralTriangle z) :=
  CoherentPathCoordinates.tetrahedronTraceAgainst_skipSecond
    (circleCompanionComparisonTetrahedron_two z k)

/-- 正方形の右辺は、元の apex 辺と元の companion 三角形の trace の豊穣合成。 -/
lemma circleCompanionComparisonHomSquare_includeFirst (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      circleCompanionComparisonHomSquare z k =
    lift (CoherentPathCoordinates.tetrahedronInitialTrace
        (circleCompanionComparisonTetrahedron z k))
      (CoherentPathCoordinates.triangleTrace (circleCompanionReflectedTriangle z k) ≫
        eqToHom (congrArg (fun s : (SimplicialNerve OmegaSpectrum.{u}) _⦋2⦌ ↦
          SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
          (circleCompanionComparisonTetrahedron_zero z k).symm)) ≫
      eComp SSet ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 0⟩)
        ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 1⟩)
        ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 3⟩) ≫
      eqToHom (congrArg (fun s : (SimplicialNerve OmegaSpectrum.{u}) _⦋2⦌ ↦
        SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
        (circleCompanionComparisonTetrahedron_two z k)) := by
  rw [circleCompanionComparisonHomSquare, CoherentPathCoordinates.tetrahedronTraceAgainst,
    ← Category.assoc, CoherentPathCoordinates.tetrahedronTrace_includeFirst_face
      (circleCompanionComparisonTetrahedron_zero z k)]
  simp only [Category.assoc]

/-- 正方形の上辺は、元の一点上の比較三角形と元の底の辺の豊穣合成。 -/
lemma circleCompanionComparisonHomSquare_includeSecond (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      circleCompanionComparisonHomSquare z k =
    lift (CoherentPathCoordinates.triangleTrace (circleCompanionComparisonBranchTriangle z k) ≫
        eqToHom (congrArg (fun s : (SimplicialNerve OmegaSpectrum.{u}) _⦋2⦌ ↦
          SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
          (circleCompanionComparisonTetrahedron_three z k).symm))
      (CoherentPathCoordinates.tetrahedronFinalTrace (circleCompanionComparisonTetrahedron z k)) ≫
      eComp SSet ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 0⟩)
        ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 2⟩)
        ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 3⟩) ≫
      eqToHom (congrArg (fun s : (SimplicialNerve OmegaSpectrum.{u}) _⦋2⦌ ↦
        SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
        (circleCompanionComparisonTetrahedron_two z k)) := by
  rw [circleCompanionComparisonHomSquare, CoherentPathCoordinates.tetrahedronTraceAgainst,
    ← Category.assoc, CoherentPathCoordinates.tetrahedronTrace_includeSecond_face
      (circleCompanionComparisonTetrahedron_three z k)]
  simp only [Category.assoc]

end SerrePositivity.KST.Spectra.OmegaSpectrum
