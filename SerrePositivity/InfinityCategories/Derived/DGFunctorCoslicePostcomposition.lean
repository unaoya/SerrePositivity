module
public import SerrePositivity.InfinityCategories.Derived.DGClosedCoslicePrecomposition
public import SerrePositivity.InfinityCategories.F1.CoslicePostcompTransport
public import SerrePositivity.InfinityCategories.DGNerve.Functor
/-!
概要：同じ dg 関手による実 coslice の後合成を、対象の標準点に正規化する。
方針：実 dg 頂点の像を照合し、join 族の同じ後合成と射影を保存する。
規約：対象宇宙を共通にする。使われ方：実 Hom の全関手族の coslice 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  (F : DGFunctor R D E) (x : D)
/-- 元の同じ dg 頂点の点図式は、関手像の標準点に移る。 -/
lemma dgFunctorPointDiagram :
    (SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex x) ≫ dgNerve.map F =
      (SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex (F.obj x)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Simplex.vertexEquiv.injective
  rfl
/-- 同じ dg 関手による、標準点に正規化した実 coslice の後合成。 -/
def dgFunctorCoslicePostcomp : dgVertexCoslice R D x ⟶ dgVertexCoslice R E (F.obj x) :=
  stableCoslicePostcomp _ (dgNerve.map F) _ (dgFunctorPointDiagram R F x)
/-- 実後合成は同じ dg nerve 関手を底に持つ。 -/
lemma dgFunctorCoslicePostcomp_projection :
    dgFunctorCoslicePostcomp R F x ≫ sliceUnderProjection
      ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex (F.obj x))) =
    sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
      (Simplex.vertex x)) ≫ dgNerve.map F :=
  stableCoslicePostcomp_projection _ _ _ _
/-- 実後合成の join 族は、元の同じ族を同じ関手で写したもの。 -/
lemma dgFunctorCoslicePostcomp_val {n : ℕ} (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    ((dgFunctorCoslicePostcomp R F x).app _ σ).val = σ.val ≫ dgNerve.map F := by
  have H {X Y : SSet.{max u v}} (a : Δ[0] ⟶ X) (f : X ⟶ Y) (b : Δ[0] ⟶ Y)
      (h : a ≫ f = b) (τ : (sliceUnder a) _⦋n⦌) :
      ((stableCoslicePostcomp a f b h).app _ τ).val = τ.val ≫ f := by
    subst b
    rfl
  exact H _ _ _ _ σ
/-- 座標単体も元の同じ dg nerve 関手による像に一致する。 -/
lemma dgFunctorCoslicePostcomp_coordinate {n : ℕ} (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    dgPointCosliceSimplex _ ((dgFunctorCoslicePostcomp R F x).app _ σ) =
      dgPointCosliceSimplex _ σ ≫ dgNerve.map F := by
  change (leftPointStdSimplexIso n).inv ≫ ((dgFunctorCoslicePostcomp R F x).app _ σ).val =
    ((leftPointStdSimplexIso n).inv ≫ σ.val) ≫ dgNerve.map F
  rw [dgFunctorCoslicePostcomp_val, Category.assoc]
end SerrePositivity.InfinityCategories
