module
public import SerrePositivity.InfinityCategories.Derived.DGClosedCosliceCoordinates
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (x q : D) (s : ForgetEnrichment.of (Complex R) q ⟶ ForgetEnrichment.of (Complex R) x)
/-- 同じ閉始点置換の実 coslice 単体は全面・退化と可換。 -/
lemma dgCoslicePrecomposeSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (dgVertexCoslice R D x) _⦋n⦌) :
    (dgVertexCoslice R D q).map α.op (dgCoslicePrecomposeSimplex R D x q s σ) =
      dgCoslicePrecomposeSimplex R D x q s ((dgVertexCoslice R D x).map α.op σ) := by
  apply dgPointCosliceSimplex_injective
    ((SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex q))
  rw [← dgPointCosliceSimplex_naturality]
  change SSet.stdSimplex.map _ ≫ dgPointCosliceSimplex _
    (dgPointCosliceSimplexOfFixed _ _ _) = dgPointCosliceSimplex _
      (dgPointCosliceSimplexOfFixed _ _ _)
  rw [dgPointCosliceSimplexOfFixed_simplex, dgPointCosliceSimplexOfFixed_simplex,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg SSet.yonedaEquiv.symm
    (dgCoslicePrecomposeCoordinate_naturality R D x q s α σ)
/-- 同じ閉射を始点に前合成する、実 coslice 全体の写像。 -/
def dgCoslicePrecompose : dgVertexCoslice R D x ⟶ dgVertexCoslice R D q where
  app n := ↾(dgCoslicePrecomposeSimplex R D x q s)
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro σ
    exact (dgCoslicePrecomposeSimplex_naturality R D x q s α.unop σ).symm
/-- 同じ実始点前合成は、元の同じ底への射影を厳密に保つ。 -/
lemma dgCoslicePrecompose_projection :
    dgCoslicePrecompose R D x q s ≫ sliceUnderProjection
      ((SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex q)) =
    sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex x)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change (sliceUnderProjection _).app _ (dgCoslicePrecomposeSimplex R D x q s σ) = _
  rw [← dgPointCosliceSimplex_projection, ← dgPointCosliceSimplex_projection]
  change SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ dgPointCosliceSimplex _
    (dgPointCosliceSimplexOfFixed _ _ _)) = _
  erw [dgPointCosliceSimplexOfFixed_simplex, ← SSet.yonedaEquiv_naturality,
    Equiv.apply_symm_apply, ← SSet.yonedaEquiv_naturality]
  exact dgSimplexInitialRefinement_face_zero R D _ q _
end SerrePositivity.InfinityCategories
