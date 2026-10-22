module

public import SerrePositivity.InfinityCategories.F2.SpaceCompositionTetrahedronInitialAction
public import SerrePositivity.InfinityCategories.F2.CoherentCompositionTetrahedronStrictFace
public import SerrePositivity.InfinityCategories.F2.SimplexPrismZeroFace
public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedFamilyBoundary

/-!
概要：元の比較三単体の零面を、同じ全係数の実 pointed 延長として保持する。
方針：元の三単体の族を制限し、図式と始点を実際の等式で回収する。
規約：最大化三角形の標準族との等式を仮定しない。
使われ方：始点固定延長空間の指定比較へ零面を入力する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "T" => coherentCompositionTetrahedron s
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))

/-- 元の三単体の全係数族を零面へ制限した実際の pointed 族。 -/
def spaceCompositionTetrahedronZeroFamily :
    (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u} :=
  (stdSimplex.δ (0 : Fin 4) ▷ A) ≫ spaceSimplexPointedFamily T

/-- 零面の図式は同じ元の三角形の最大 path 表示。 -/
lemma spaceCompositionTetrahedronZeroFamily_projection :
    spaceCompositionTetrahedronZeroFamily s ≫ pointedSpaceProjection =
      fst Δ[2] A ≫ SSet.yonedaEquiv.symm (coherentSimplexMaximalization s) := by
  have hp : spaceSimplexPointedFamily T ≫ pointedSpaceProjection =
      fst Δ[3] A ≫ SSet.yonedaEquiv.symm T := spaceSimplexPointedFamily_projection T
  have hf : (stdSimplex.δ (0 : Fin 4) ▷ A) ≫
      (fst Δ[3] A ≫ SSet.yonedaEquiv.symm T) =
        fst Δ[2] A ≫ (stdSimplex.δ (0 : Fin 4) ≫ SSet.yonedaEquiv.symm T) := by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f ↦ (stdSimplex.δ (0 : Fin 4) ▷ A) ≫ f) hp).trans
      (hf.trans (congrArg (fun f ↦ fst Δ[2] A ≫ f)
        ((SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ (0 : Fin 4)) T).trans
          (congrArg SSet.yonedaEquiv.symm (coherentCompositionTetrahedron_face_zero s))))))

/-- 零面の始点は同じ全 Hom 係数の元の標準 fiber 比較。 -/
lemma spaceCompositionTetrahedronZeroFamily_initial :
    (scaffoldFirstVertex 2 ▷ A) ≫ spaceCompositionTetrahedronZeroFamily s =
      snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
        vertexFiberι pointedSpaceProjection (coherentNerveVertex K) := by
  unfold spaceCompositionTetrahedronZeroFamily
  rw [← Category.assoc]
  have hi : (scaffoldFirstVertex 2 ▷ A) ≫ (stdSimplex.δ (0 : Fin 4) ▷ A) =
      snd Δ[0] A ≫ simplexPrismVertex 3 1 A := by
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc,
      simplexPrismVertex_first_face_zero]
  rw [hi, Category.assoc, spaceCompositionTetrahedron_second_action]

end SerrePositivity.InfinityCategories.F2
