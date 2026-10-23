module
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberCoordinates
/-!
概要：実 coslice の全単体を、最初の頂点を固定した元の一つ上の単体へ移す。
方針：左の点との join 同型で座標化し、全添字変更と射影を照合する。
規約：対象は任意の単体集合。使われ方：dg 始点細分による Hom の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)
/-- 実 coslice 単体の、元の一つ上の単体としての座標。 -/
def dgPointCosliceSimplex {n : ℕ} (σ : (sliceUnder a) _⦋n⦌) : Δ[n + 1] ⟶ X :=
  (leftPointStdSimplexIso n).inv ≫ σ.val
/-- 同じ座標は最初の頂点で指定点を回収する。 -/
lemma dgPointCosliceSimplex_fixed {n : ℕ} (σ : (sliceUnder a) _⦋n⦌) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
      dgPointCosliceSimplex a σ = a := by
  rw [dgPointCosliceSimplex, ← Category.assoc, leftPointStdSimplexIso_first_inv]
  exact σ.property
/-- 同じ座標は全次数で実 coslice 単体を区別する。 -/
lemma dgPointCosliceSimplex_injective {n : ℕ} {σ τ : (sliceUnder a) _⦋n⦌}
    (h : dgPointCosliceSimplex a σ = dgPointCosliceSimplex a τ) : σ = τ := by
  apply Subtype.ext
  exact (cancel_epi (leftPointStdSimplexIso n).inv).mp h
/-- 全ての面・退化は、最初の頂点を固定する番号変更に移る。 -/
lemma dgPointCosliceSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (sliceUnder a) _⦋n⦌) :
    stdSimplex.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)) ≫
      dgPointCosliceSimplex a σ = dgPointCosliceSimplex a ((sliceUnder a).map α.op σ) := by
  change stdSimplex.map _ ≫ ((leftPointStdSimplexIso n).inv ≫ σ.val) =
    (leftPointStdSimplexIso m).inv ≫ (joinMap (𝟙 Δ[0]) (stdSimplex.map α) ≫ σ.val)
  rw [← Category.assoc, leftPointStdSimplexIso_inv_naturality, Category.assoc]
/-- 同じ射影は、座標単体の零面に一致する。 -/
lemma dgPointCosliceSimplex_projection {n : ℕ} (σ : (sliceUnder a) _⦋n⦌) :
    SSet.yonedaEquiv (stdSimplex.δ 0 ≫ dgPointCosliceSimplex a σ) =
      (sliceUnderProjection a).app _ σ := by
  rw [dgPointCosliceSimplex, ← Category.assoc, leftPointStdSimplexIso_face_inv]
  rfl
/-- 最初の頂点が固定された単体から、同じ実 coslice 単体を回収する。 -/
def dgPointCosliceSimplexOfFixed {n : ℕ} (F : Δ[n + 1] ⟶ X)
    (hF : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫ F = a) :
    (sliceUnder a) _⦋n⦌ :=
  ⟨(leftPointStdSimplexIso n).hom ≫ F, by
    rw [← Category.assoc, joinStdSimplexIso_leftPoint_inl]
    exact hF⟩
/-- 実 coslice への回収は、元の同じ座標単体を保つ。 -/
lemma dgPointCosliceSimplexOfFixed_simplex {n : ℕ} (F : Δ[n + 1] ⟶ X)
    (hF : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫ F = a) :
    dgPointCosliceSimplex a (dgPointCosliceSimplexOfFixed a F hF) = F := by
  change (leftPointStdSimplexIso n).inv ≫ ((leftPointStdSimplexIso n).hom ≫ F) = F
  rw [Iso.inv_hom_id_assoc]
end SerrePositivity.InfinityCategories
