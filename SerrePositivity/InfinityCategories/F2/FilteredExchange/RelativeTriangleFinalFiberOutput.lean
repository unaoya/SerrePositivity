module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionCurryTargetCoordinates
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionCurryIsoImage

/-!
概要：全三角形の図式辺と長辺の切断を、同じ最後の小さい fiber で評価して比較する。
方針：元の全延長空間からの写像の pointed 座標と、二面が共有する最終頂点を照合する。
規約：指定同型を写す元の写像自体の等式。使われ方：切断模型と prism 模型の指定類の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 三角形の図式辺と長辺は、全パラメータを保って同じ最終頂点を共有する。 -/
lemma trianglePrismFinalVertex_eq (A : SSet.{u}) :
    prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) =
      prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    rfl
  · rfl

variable {B : SSet.{u}} {A I : SSet.{u + 1}}
  (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (i : I ⟶ (Δ[2] : SSet.{u + 1}) ⊗ A) (v : I ⟶ PointedSpaceInfinity.{u})
  (hv : v ≫ pointedSpaceProjection = i ≫ (fst Δ[2] A ≫ D))

/-- 全三角形の指定面から、元の最後の小さい fiber の関手空間への評価写像。 -/
def relativeTriangleFinalFiberOutput (face : Fin 3)
    (he : (stdSimplex.δ face ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b)) :=
  relativeExtensionCurryRestriction pointedSpaceProjection (fst Δ[2] A ≫ D) i v hv
    (stdSimplex.δ face ▷ A) (stdSimplex.δ face ≫ D)
    (by rw [← Category.assoc, whiskerRight_fst, Category.assoc]) ≫
      (ihom A).map (pointedSectionTargetFiber J b (stdSimplex.δ face ≫ D) he)

/-- 図式辺と長辺の終点評価は、全延長空間からの同じ写像である。 -/
lemma relativeTriangleFinalFiberOutput_zero_one
    (h₀ : (stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b))
    (h₁ : (stdSimplex.δ (1 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b)) :
    relativeTriangleFinalFiberOutput J b D i v hv 0 h₀ =
      relativeTriangleFinalFiberOutput J b D i v hv 1 h₁ := by
  apply uncurry_injective
  have : Mono (coherentCospanFiberPointedSource J b) := by
    rw [← coherentFiberPointedSourceIso_hom_ι J b]
    infer_instance
  apply (cancel_mono (coherentCospanFiberPointedSource J b)).1
  unfold relativeTriangleFinalFiberOutput
  rw [relativeExtensionCurryRestriction_target_pointed,
    relativeExtensionCurryRestriction_target_pointed, trianglePrismFinalVertex_eq]

/-- 全延長の実頂点の像は、同じ面の切断族の指定 fiber 評価の関手頂点である。 -/
lemma relativeTriangleFinalFiberOutput_vertex (face : Fin 3)
    (he : (stdSimplex.δ face ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b))
    (W : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = fst Δ[2] A ≫ D) (hWi : i ≫ W = v) :
    (relativeTriangleFinalFiberOutput J b D i v hv face he).app _
      (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection
        (fst Δ[2] A ≫ D) i v hv ⟨W, hW, hWi⟩) =
      functorVertex (pointedTriangleFaceSections D W hW face ≫
        pointedSectionTargetFiber J b (stdSimplex.δ face ≫ D) he) := by
  exact relativeExtensionCurryRestriction_postcomp_vertex pointedSpaceProjection
    (fst Δ[2] A ≫ D) i v hv (stdSimplex.δ face ▷ A) (stdSimplex.δ face ≫ D)
    (by rw [← Category.assoc, whiskerRight_fst, Category.assoc]) W hW hWi _

end SerrePositivity.InfinityCategories.F2
