module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowCancellationPrism

/-!
概要：元の合成三角形から、射圏内の元の全 pushout 四角形を構成する。
方針：二つの評価をそれぞれ縦・横に退化した pushout とし、点ごとの普遍性を使う。
規約：元の最初の辺・合成辺・最後の辺を指定頂点として保持する。
使われ方：実像の二対三則の左消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u}}

/-- 元の任意の横辺を縦に恒等として伸ばした四角形も、元の全 pushout。 -/
lemma firstProjection_isPushoutSquare [Quasicategory C] (g : (Δ[1] : SSet.{u}) ⟶ C) :
    IsPushoutSquare (fst Δ[1] Δ[1] ≫ g) := by
  have h := (isPushoutSquare_iff_transpose (snd Δ[1] Δ[1] ≫ g)).mp
    (secondProjection_isPushoutSquare g)
  exact h

/-- 元の合成三角形を、元の射圏内の全四角形へ送る。 -/
def arrowCancellationFamily (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  curry (arrowCancellationPrism ≫ σ)

/-- 始点評価は最初の辺の退化四角形。 -/
lemma arrowCancellationFamily_zero (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    arrowCancellationFamily σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      fst Δ[1] Δ[1] ≫ stdSimplex.δ (2 : Fin 3) ≫ σ := by
  rw [arrowCancellationFamily, curry_evaluateFunctorAt_vertex]
  change prismEndpoint 0 _ ≫ (arrowCancellationPrism ≫ σ) = _
  rw [← Category.assoc, arrowCancellationPrism_zero, Category.assoc]

/-- 終点評価は最後の辺の退化四角形。 -/
lemma arrowCancellationFamily_one (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    arrowCancellationFamily σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
      snd Δ[1] Δ[1] ≫ stdSimplex.δ (0 : Fin 3) ≫ σ := by
  rw [arrowCancellationFamily, curry_evaluateFunctorAt_vertex]
  change prismEndpoint 1 _ ≫ (arrowCancellationPrism ≫ σ) = _
  rw [← Category.assoc, arrowCancellationPrism_one, Category.assoc]

/-- 元の合成三角形は、射圏内の同じ指定四角形を pushout にする。 -/
lemma arrowCancellationFamily_isPushout [Quasicategory C] (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    IsPushoutSquare (arrowCancellationFamily σ) := by
  apply isColimitCone_functor_of_pointwise
  intro v
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
  have hj : IsPushoutSquare
      (arrowCancellationFamily σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) := by
    fin_cases j
    · change IsPushoutSquare
        (arrowCancellationFamily σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      rw [arrowCancellationFamily_zero]
      exact firstProjection_isPushoutSquare (stdSimplex.δ (2 : Fin 3) ≫ σ)
    · change IsPushoutSquare
        (arrowCancellationFamily σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      rw [arrowCancellationFamily_one]
      exact secondProjection_isPushoutSquare (stdSimplex.δ (0 : Fin 3) ≫ σ)
  exact (F2.isColimitCone_iff_of_coconeMap_eq _
    (pushoutCocone (arrowCancellationFamily σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)))
    (Category.assoc _ _ _)).mpr hj

/-- 左下頂点は元の最初の辺。 -/
lemma arrowCancellationFamily_vertex_first (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    (arrowCancellationFamily σ).app _
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
        functorVertex (stdSimplex.δ (2 : Fin 3) ≫ σ) := by
  rw [arrowCancellationFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowCancellationPrism _ ≫ σ) = _
  rw [arrowCancellationPrism_vertex_first]

/-- 右下頂点は元の中間対象の恒等射。 -/
lemma arrowCancellationFamily_vertex_identity (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    (arrowCancellationFamily σ).app _
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) =
        functorVertex (SSet.const (σ.app _ (stdSimplex.obj₀Equiv.symm (1 : Fin 3)))) := by
  rw [arrowCancellationFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowCancellationPrism _ ≫ σ) = _
  rw [arrowCancellationPrism_vertex_identity, SSet.const_comp]

/-- 左上頂点は元の合成辺。 -/
lemma arrowCancellationFamily_vertex_composite (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    (arrowCancellationFamily σ).app _
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) =
        functorVertex (stdSimplex.δ (1 : Fin 3) ≫ σ) := by
  rw [arrowCancellationFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowCancellationPrism _ ≫ σ) = _
  rw [arrowCancellationPrism_vertex_composite]

/-- 右上頂点は元の最後の辺。 -/
lemma arrowCancellationFamily_vertex_last (σ : (Δ[2] : SSet.{u}) ⟶ C) :
    (arrowCancellationFamily σ).app _
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) =
        functorVertex (stdSimplex.δ (0 : Fin 3) ≫ σ) := by
  rw [arrowCancellationFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowCancellationPrism _ ≫ σ) = _
  rw [arrowCancellationPrism_vertex_last]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
