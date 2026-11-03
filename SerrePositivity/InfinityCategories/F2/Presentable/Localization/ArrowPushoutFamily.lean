module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowPushoutPrism
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.DegeneratePushoutSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalPrismRestriction
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.FunctorCoconePointwiseCriterion

/-!
概要：元の pushout 四角形を、射圏内の実 pushout 四角形へ写す。
方針：最小値 prism を curry し、零時刻の退化 pushout と一時刻の元の pushout で判定。
規約：元の下辺・上辺と二本の恒等射を、全関手の頂点として厳密に保持する。
使われ方：射圏内の span 余極限閉性から、辺クラスの pushout 保存への接続。
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

/-- 元の四角形を恒等射・下辺・上辺からなる射圏内の四角形へ写す。 -/
def arrowPushoutFamily (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  curry (arrowPushoutPrism ≫ R)

/-- 零端評価は、元の左辺を横へ恒等として伸ばす退化四角形。 -/
lemma arrowPushoutFamily_zero (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    arrowPushoutFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      snd Δ[1] Δ[1] ≫ squareLeftEdge ≫ R := by
  rw [arrowPushoutFamily, curry_evaluateFunctorAt_vertex]
  change prismEndpoint 0 _ ≫ (arrowPushoutPrism ≫ R) = _
  rw [← Category.assoc, arrowPushoutPrism_zero, Category.assoc]

/-- 一端評価は元の四角形そのもの。 -/
lemma arrowPushoutFamily_one (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    arrowPushoutFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = R := by
  rw [arrowPushoutFamily, curry_evaluateFunctorAt_vertex]
  change prismEndpoint 1 _ ≫ (arrowPushoutPrism ≫ R) = _
  rw [← Category.assoc, arrowPushoutPrism_one, Category.id_comp]

/-- 元の pushout は、同じ四角形パラメータの射圏内でも実 pushout を与える。 -/
lemma arrowPushoutFamily_isPushout [Quasicategory C]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) (hR : IsPushoutSquare R) :
    IsPushoutSquare (arrowPushoutFamily R) := by
  apply isColimitCone_functor_of_pointwise
  intro v
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
  have hj : IsPushoutSquare
      (arrowPushoutFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) := by
    fin_cases j
    · change IsPushoutSquare
        (arrowPushoutFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      rw [arrowPushoutFamily_zero]
      exact secondProjection_isPushoutSquare (squareLeftEdge ≫ R)
    · change IsPushoutSquare
        (arrowPushoutFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      rw [arrowPushoutFamily_one]
      exact hR
  exact (F2.isColimitCone_iff_of_coconeMap_eq _
    (pushoutCocone (arrowPushoutFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)))
    (Category.assoc _ _ _)).mpr hj

/-- 左下の頂点は、元の左下対象上の恒等射。 -/
lemma arrowPushoutFamily_vertex_zero (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    (arrowPushoutFamily R).app _
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
        functorVertex (SSet.const (R.app _
          (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0))) := by
  rw [arrowPushoutFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowPushoutPrism _ ≫ R) = _
  rw [arrowPushoutPrism_vertex_zero, SSet.const_comp]

/-- 右下の頂点は元の指定下辺。 -/
lemma arrowPushoutFamily_vertex_bottom (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    (arrowPushoutFamily R).app _
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) =
        functorVertex (squareBottomEdge ≫ R) := by
  rw [arrowPushoutFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowPushoutPrism _ ≫ R) = _
  rw [arrowPushoutPrism_vertex_bottom]

/-- 左上の頂点は、元の左上対象上の恒等射。 -/
lemma arrowPushoutFamily_vertex_left (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    (arrowPushoutFamily R).app _
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) =
        functorVertex (SSet.const (R.app _
          (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1))) := by
  rw [arrowPushoutFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowPushoutPrism _ ≫ R) = _
  rw [arrowPushoutPrism_vertex_left, SSet.const_comp]

/-- 右上の頂点は元の指定上辺。 -/
lemma arrowPushoutFamily_vertex_top (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    (arrowPushoutFamily R).app _
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) =
        functorVertex (squareTopEdge ≫ R) := by
  rw [arrowPushoutFamily, curry_vertex_prismEvaluation]
  change functorVertex (prismVertexEvaluation arrowPushoutPrism _ ≫ R) = _
  rw [arrowPushoutPrism_vertex_top]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
