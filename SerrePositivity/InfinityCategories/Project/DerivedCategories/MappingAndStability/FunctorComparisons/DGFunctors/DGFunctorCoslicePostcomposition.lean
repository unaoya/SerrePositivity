module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedCoslicePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostcompTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (x : D)
/-- 元の同じ dg 頂点の点図式は、関手像の標準点に移る。 -/
lemma dgFunctorPointDiagram :
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl
/-- 同じ dg 関手による、標準点に正規化した実 coslice の後合成。 -/
def dgFunctorCoslicePostcomp : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D x ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R E (F.obj x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) _ (dgFunctorPointDiagram R F x)
/-- 実後合成は同じ dg nerve 関手を底に持つ。 -/
lemma dgFunctorCoslicePostcomp_projection :
    dgFunctorCoslicePostcomp R F x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_projection _ _ _ _
/-- 実後合成の join 族は、元の同じ族を同じ関手で写したもの。 -/
lemma dgFunctorCoslicePostcomp_val {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D x) _⦋n⦌) :
    ((dgFunctorCoslicePostcomp R F x).app _ σ).val = σ.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  have H {X Y : SSet.{max u v}} (a : Δ[0] ⟶ X) (f : X ⟶ Y) (b : Δ[0] ⟶ Y)
      (h : a ≫ f = b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋n⦌) :
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp a f b h).app _ τ).val = τ.val ≫ f := by
    subst b
    rfl
  exact H _ _ _ _ σ
/-- 座標単体も元の同じ dg nerve 関手による像に一致する。 -/
lemma dgFunctorCoslicePostcomp_coordinate {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D x) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex _ ((dgFunctorCoslicePostcomp R F x).app _ σ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex _ σ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫ ((dgFunctorCoslicePostcomp R F x).app _ σ).val =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫ σ.val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F
  rw [dgFunctorCoslicePostcomp_val, Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
