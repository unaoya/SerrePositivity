module

public import SerrePositivity.KST.Spectra.SpectrumCircleTetrahedronTrace
public import SerrePositivity.KST.Spectra.CoherentSimplexCompositionFaces
public import SerrePositivity.KST.Spectra.CoherentTriangleDegenerateTrace

/-!
概要：元の円評価の Hom 正方形の残る二辺を、元の参照面・退化面の合成で計算する。
方針：各面の厳密式で Hom の端点を移送し、元の三単体の合成式を適用する。
規約：充填・辺・三角形を選び直さない。使われ方：元の零三角形の差と BK 錐の比較。
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
open CoherentPathCoordinates
local instance circleCompositionTraceSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の参照零三角形の経路を、元の三単体の零番目の面の端点へ移送したもの。 -/
def circleEvaluationReferenceTrace (z : Sp.{u} _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⟶
      SimplicialCategory.sHom ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 1⟩)
        ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 3⟩) :=
  triangleTrace (SSet.yonedaEquiv (circleZeroFunctorTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z)) ≫
    eqToHom (congrArg (fun s : Sp.{u} _⦋2⦌ ↦
      SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
        (circleEvaluationTetrahedronAt_zero z).symm)

/-- 元の退化零三角形の経路を、元の三単体の三番目の面の端点へ移送したもの。 -/
def circleEvaluationDegenerateTrace (z : Sp.{u} _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⟶
      SimplicialCategory.sHom ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 0⟩)
        ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 2⟩) :=
  triangleTrace (SSet.yonedaEquiv (circleZeroDegenerateTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z)) ≫
    eqToHom (congrArg (fun s : Sp.{u} _⦋2⦌ ↦
      SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
        (circleEvaluationTetrahedronAt_three z).symm)

/-- 元の退化零三角形の移送後の経路も、元の Hom 内の定値経路。 -/
lemma circleEvaluationDegenerateTrace_constant (z : Sp.{u} _⦋0⦌) :
    ∃ y, circleEvaluationDegenerateTrace z = SSet.const y := by
  obtain ⟨y, hy⟩ := triangleTrace_constant_of_eq_degenerateZero
    (circleZeroDegenerateTriangleAt z)
  unfold circleEvaluationDegenerateTrace
  erw [hy, SSet.const_comp]
  exact ⟨_, rfl⟩

/-- 元の三単体の長い Hom の端点を、元の cotensor と入力へ正規化する移送射。 -/
def circleEvaluationHomTransport (z : Sp.{u} _⦋0⦌) :
    SimplicialCategory.sHom ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 0⟩)
        ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 3⟩) ⟶
      mappingSpace (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
          (nativeCotensorInput PointedSimplicialSet.circle z).val :=
  eqToHom (congrArg (fun s : Sp.{u} _⦋2⦌ ↦
    SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
      (circleEvaluationTetrahedronAt_two z))

/-- 第一座標一の辺は、元の最初の辺と参照零三角形の経路の豊穣合成。 -/
lemma circleEvaluationHomSquare_includeFirst (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        circleEvaluationHomSquare z =
      lift (tetrahedronInitialTrace (circleEvaluationTetrahedronAt z))
        (circleEvaluationReferenceTrace z) ≫
        eComp SSet ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 0⟩)
          ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 1⟩)
          ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 3⟩) ≫
        circleEvaluationHomTransport z := by
  change _ ≫ (tetrahedronTrace (circleEvaluationTetrahedronAt z) ≫ _) = _
  rw [← Category.assoc,
    tetrahedronTrace_includeFirst_face (circleEvaluationTetrahedronAt_zero z)]
  rfl

/-- 第二座標一の辺は、元の退化零三角形の経路と最後の辺の豊穣合成。 -/
lemma circleEvaluationHomSquare_includeSecond (z : Sp.{u} _⦋0⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        circleEvaluationHomSquare z =
      lift (circleEvaluationDegenerateTrace z)
        (tetrahedronFinalTrace (circleEvaluationTetrahedronAt z)) ≫
        eComp SSet ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 0⟩)
          ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 2⟩)
          ((circleEvaluationTetrahedronAt z).obj ⟨ULift.up 3⟩) ≫
        circleEvaluationHomTransport z := by
  change _ ≫ (tetrahedronTrace (circleEvaluationTetrahedronAt z) ≫ _) = _
  rw [← Category.assoc,
    tetrahedronTrace_includeSecond_face (circleEvaluationTetrahedronAt_three z)]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
