module

public import SerrePositivity.KST.Spectra.CoherentSimplexTraceFaces
public import SerrePositivity.KST.Spectra.SpectrumCircleTetrahedronSimplex

/-!
概要：元の円評価三単体から Hom 正方形を取り出し、生成 loop の辺を保持する。
方針：元の二番目の面の等式で端点を移送し、比較単体の経路を計算する。
規約：元の充填を変更しない。使われ方：元の円評価錐と BK 極限錐の比較。
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
local instance circleTetrahedronTraceSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の円評価三単体の Hom 正方形。二番目の面で端点を元の cotensor と入力へ同定。 -/
def circleEvaluationHomSquare (z : Sp.{u} _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      mappingSpace (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
          (nativeCotensorInput PointedSimplicialSet.circle z).val :=
  tetrahedronTraceAgainst (circleEvaluationTetrahedronAt_two z)

/-- 第二座標零の辺は、元の普遍評価の同じ生成 loop の一単体。 -/
lemma circleEvaluationHomSquare_skipSecond (z : Sp.{u} _⦋0⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        circleEvaluationHomSquare z =
      SSet.yonedaEquiv.symm
        ((circleEvaluationHomEdge
          (nativeCotensorInput PointedSimplicialSet.circle z).val).edge) := by
  change _ ≫ tetrahedronTraceAgainst (circleEvaluationTetrahedronAt_two z) = _
  rw [tetrahedronTraceAgainst_skipSecond, triangleTrace_comparison]
  rfl

/-- 元の companion 三角形の Hom 経路。元の二つの面の等式で端点を移送する。 -/
def circleEvaluationCompanionHomPath (z : Sp.{u} _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⟶
      mappingSpace (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
          (nativeCotensorInput PointedSimplicialSet.circle z).val :=
  triangleTrace (SSet.yonedaEquiv (circleZeroCompanionTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z)) ≫
    eqToHom ((congrArg
      (fun s : Sp.{u} _⦋2⦌ ↦
        SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
      (circleEvaluationTetrahedronAt_one z)).symm.trans
        (congrArg (fun s : Sp.{u} _⦋2⦌ ↦
          SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
            (circleEvaluationTetrahedronAt_two z)))

/-- 第一座標零の辺は、元の四角形の companion 三角形の同じ Hom 経路。 -/
lemma circleEvaluationHomSquare_skipFirst (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        circleEvaluationHomSquare z = circleEvaluationCompanionHomPath z := by
  unfold circleEvaluationHomSquare tetrahedronTraceAgainst circleEvaluationCompanionHomPath
  rw [← Category.assoc, tetrahedronTrace_skipFirst]
  exact triangleTrace_transport (circleEvaluationTetrahedronAt_one z) _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum
