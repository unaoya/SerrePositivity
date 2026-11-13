module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGPointCosliceCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementInitialMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementCongruence
/-!
概要：閉始点細分を、最初の頂点を固定した実 coslice の座標に適用する。
方針：元の単体を回収し、同じ閉射の等式輸送で始点を置換する。
規約：全次数・全単体作用を保つ。使われ方：実 Hom の全関手族の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  (x q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x)
/-- 指定 dg 対象の実頂点を始点とする coslice。 -/
abbrev dgVertexCoslice := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
/-- 同じ実 coslice 単体の dg 単体座標。 -/
def dgCosliceCoordinate {n : ℕ} (σ : (dgVertexCoslice R D x) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D (n + 1) :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex _ σ)
/-- 元の同じ座標単体の始対象は指定対象。 -/
lemma dgCosliceCoordinate_obj_zero {n : ℕ} (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    (dgCosliceCoordinate R D x σ).obj 0 = x := by
  have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex_fixed _ σ)
  rw [← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply] at h
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 0 ↦ t.obj 0) h

/-- 同じ閉射で始点を置換した実座標単体。 -/
def dgCoslicePrecomposeCoordinate {n : ℕ} (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement R D (dgCosliceCoordinate R D x σ) q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport R D s (dgCosliceCoordinate_obj_zero R D x σ).symm)
/-- 置換後の座標単体は同じ新始点を保つ。 -/
lemma dgCoslicePrecomposeCoordinate_fixed {n : ℕ} (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
        (dgCoslicePrecomposeCoordinate R D x q s σ) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) := by
  apply SSet.yonedaEquiv.injective
  rw [← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  change (dgCoslicePrecomposeCoordinate R D x q s σ).obj 0 = q
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_obj_zero R D (dgCosliceCoordinate R D x σ) q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport R D s (dgCosliceCoordinate_obj_zero R D x σ).symm)
/-- 同じ閉始点置換による実 coslice 単体。 -/
def dgCoslicePrecomposeSimplex {n : ℕ} (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    (dgVertexCoslice R D q) _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplexOfFixed _
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
      (dgCoslicePrecomposeCoordinate R D x q s σ))
    (dgCoslicePrecomposeCoordinate_fixed R D x q s σ)
/-- 元の座標は全ての面・退化に自然。 -/
lemma dgCosliceCoordinate_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    dgCosliceCoordinate R D x ((dgVertexCoslice R D x).map α.op σ) =
      (dgCosliceCoordinate R D x σ).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom) := by
  have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex_naturality _ α σ)
  rw [← SSet.yonedaEquiv_naturality] at h
  exact h.symm
/-- 同じ閉始点置換の座標も全単体作用に自然。 -/
lemma dgCoslicePrecomposeCoordinate_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    (dgCoslicePrecomposeCoordinate R D x q s σ).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom) =
      dgCoslicePrecomposeCoordinate R D x q s ((dgVertexCoslice R D x).map α.op σ) := by
  unfold dgCoslicePrecomposeCoordinate
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_pullback_initial R D _ q _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom_zero _) (by
      intro i hi
      obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
      exact Fin.succ_ne_zero _)]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr
    (dgCosliceCoordinate_naturality R D x α σ).symm q q
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge R D _ _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge R D s _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge R D s _).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
