module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleDataNaturality
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
/-! 概要：元の評価三角形を全 Δ²×K 上で構成する。
方針：三相単体の全自然性を束ねる。
規約：全ての辺で同じ K を保持。使われ方：大域評価三角形の辺比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (normalizedTensorTriangleSimplex A X Y c τ).pullback θ.toOrderHom =
      normalizedTensorTriangleSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) (τ.comp θ.toOrderHom) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact normalizedTensorTriangleData_pullback_map A X Y c τ θ

def normalizedTensorTriangleMap :
    (Δ[2] : SSet.{u + 1}) ⊗ nerve (normalizedTensorElementIndex A X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) where
  app _ := ↾fun a => normalizedTensorTriangleSimplex A X Y a.2
    (SSet.stdSimplex.objEquiv a.1).toOrderHom
  naturality _ _ f := by
    ext a
    exact (normalizedTensorTriangleSimplex_pullback_map A X Y a.2
      (SSet.stdSimplex.objEquiv a.1).toOrderHom f.unop).symm

lemma normalizedTensorTriangleMap_app {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (t : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    (normalizedTensorTriangleMap A X Y).app (Opposite.op ⦋n⦌) (t, c) =
      normalizedTensorTriangleSimplex A X Y c (SSet.stdSimplex.objEquiv t).toOrderHom := rfl

end SerrePositivity.EInfinity.ComplexLimits
