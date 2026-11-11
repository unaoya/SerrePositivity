module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedCosliceCoordinates
/-!
概要：同じ閉射による始点細分を、実 coslice 全体の単体写像にする。
方針：全座標の自然性から写像を構成し、零面の保存で底への射影と照合する。
規約：対象の小ささも前三角性も不要。使われ方：実 Hom の全関手族の比較。
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
/-- 同じ閉始点置換の実 coslice 単体は全面・退化と可換。 -/
lemma dgCoslicePrecomposeSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D x) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D q).map α.op (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeSimplex R D x q s σ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeSimplex R D x q s ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D x).map α.op σ) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q))
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex_naturality]
  change SSet.stdSimplex.map _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplexOfFixed _ _ _) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplexOfFixed _ _ _)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplexOfFixed_simplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplexOfFixed_simplex,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeCoordinate_naturality R D x q s α σ)
/-- 同じ閉射を始点に前合成する、実 coslice 全体の写像。 -/
def dgCoslicePrecompose : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D x ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D q where
  app n := ↾(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeSimplex R D x q s)
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro σ
    exact (dgCoslicePrecomposeSimplex_naturality R D x q s α.unop σ).symm
/-- 同じ実始点前合成は、元の同じ底への射影を厳密に保つ。 -/
lemma dgCoslicePrecompose_projection :
    dgCoslicePrecompose R D x q s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection _).app _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeSimplex R D x q s σ) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex_projection, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex_projection]
  change SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplexOfFixed _ _ _)) = _
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplexOfFixed_simplex, ← SSet.yonedaEquiv_naturality,
    Equiv.apply_symm_apply, ← SSet.yonedaEquiv_naturality]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_face_zero R D _ q _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
