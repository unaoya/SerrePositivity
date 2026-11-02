module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRelativeFiberCurry
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleTargetFiberCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeCurryHomVertexEvaluation

/-!
概要：辺の切断族を curry して終点で評価する写像を、元の全 prism の直接終点評価へ同定する。
方針：同じ pointed 全族の厳密な座標を比較し、元の fiber 同型と包含の単射性を使う。
規約：元の頂点等式と全族を保持。使われ方：新しい切断の指定像と旧 prism 出力の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} {A : SSet.{u + 1}}
  (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (hv : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b))
  (ha : prismEndpoint 1 A ≫ (fst Δ[1] A ≫ e) = SSet.const (J.app _ (ULift.up b)))
local notation "R" => relativeFunctorSpace pointedSpaceProjection (fst Δ[1] A ≫ e)

/-- curry 後の終点評価と元の全族の直接終点評価は、全パラメータを保つ同じ写像。 -/
lemma pointedSectionTargetFiber_curry :
    relativeFunctorCurryHom pointedSpaceProjection e A ≫
        (ihom A).map (pointedSectionTargetFiber J b e hv) =
      relativeFunctorPre pointedSpaceProjection (fst Δ[1] A ≫ e) (prismEndpoint 1 A) ≫
        pointedRelativeFiberCurry J b (prismEndpoint 1 A ≫ (fst Δ[1] A ≫ e)) ha := by
  apply uncurry_injective
  have : Mono (coherentCospanFiberPointedSource J b) := by
    rw [← coherentFiberPointedSourceIso_hom_ι J b]
    infer_instance
  apply (cancel_mono (coherentCospanFiberPointedSource J b)).1
  have hc : pointedSectionTargetFiber J b e hv ≫ coherentCospanFiberPointedSource J b =
      relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 1) ≫
        vertexFiberι pointedSpaceProjection (e.app _ (stdSimplex.obj₀Equiv.symm 1)) := by
    rw [← coherentFiberPointedSourceIso_hom_ι J b]
    exact pointedSectionTargetFiber_pointed J b e hv
  rw [uncurry_natural_right, Category.assoc, hc]
  rw [relativeFunctorCurryHom_evaluate_ι, uncurry_natural_left, Category.assoc,
    pointedRelativeFiberCurry_pointed, ← relativeFunctorUncurry_naturality, Category.comp_id]
  exact (relativeFunctorUncurry_pre (p := pointedSpaceProjection) (𝟙 R) (prismEndpoint 1 A)).symm

end SerrePositivity.InfinityCategories.F2
