module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierConeNextFinite

/-! # 次次数の同時実充填と更新済み下次数錐の全面整合性

概要：同時実充填の全正番号面と実 apex は、同じ一つの追加分母で更新した下次数錐に合う。
方針：元の境界面の一致と追加実辺の厳密共通性で、型付き細分の差を消す。
規約：次次数の退化選択は未仮定。使われ方：有限次数錐の後続段階の充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x : D) {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet)} {N : ℕ}
variable (C : TruncatedJoinConeData f N) {m : ℕ} (τ : Fin m → K _⦋N + 1⦌)
variable (T : DGGeneralLastHornFiniteRefinement P (dgVerdierSimplexSource A D P x C.apex)
  (fun i => dgVerdierBoundaryHorn A D P x (truncatedConeNextBoundary C (τ i))))

/-- 次次数の各新単体の全正番号面は、更新済み下次数錐の同じ実単体に一致する。 -/
lemma dgVerdierConeNextSimplex_face_positive (i : Fin m) (k : Fin (N + 2)) :
    (dgVerdierOver A D P x : SSet).δ k.succ (dgVerdierConeNextSimplex A D P x C τ T i) =
      (dgVerdierConeNextLower A D P x C τ T).simplex N le_rfl (K.δ k (τ i)) := by
  have he : SSet.yonedaEquiv (boundary.ι k.succ ≫ truncatedConeNextBoundary C (τ i)) =
      C.simplex N le_rfl (K.δ k (τ i)) := by
    rw [truncatedConeNextBoundary_face_positive, Equiv.apply_symm_apply]
  have hf := dgVerdierBoundaryRefinedSimplex_face_positive A D P x
    (truncatedConeNextBoundary C (τ i)) (T.residuals i).q (T.residuals i).s
    (T.filler i) (T.filler_fac i) (T.residuals i).denominator k.succ (Fin.succ_ne_zero k)
  refine hf.trans ?_
  change _ = dgVerdierConeRefinedSimplex A D P x C T.q T.s T.denominator N le_rfl (K.δ k (τ i))
  unfold dgVerdierConeRefinedSimplex
  apply dgVerdierSimplexInitialRefinement_congr P x he (T.residuals i).q T.q
  exact (dgClosedTargetTransport_edge A D (T.residuals i).s _).trans
    ((T.denominator_edge_eq i).trans
      (dgVerdierConeRefinementMap_edge A D P x C T.q T.s N le_rfl (K.δ k (τ i))).symm)

/-- 次次数の全新単体の実始頂点は、更新済み下次数錐の同じ実 apex。 -/
lemma dgVerdierConeNextSimplex_first_vertex (i : Fin m) :
    (dgVerdierOver A D P x : SSet).map (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op
        (dgVerdierConeNextSimplex A D P x C τ T i) =
      (dgVerdierConeNextLower A D P x C τ T).apex := by
  have he : SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0 =
      SimplexCategory.const ⦋0⦌ ⦋N + 1⦌ 0 ≫
        SimplexCategory.δ (0 : Fin (N + 2)).succ := by
    apply SimplexCategory.Hom.ext_zero_left
    exact (dgPositiveCoface_zero (0 : Fin (N + 2)).succ (Fin.succ_ne_zero _)).symm
  rw [he, op_comp, Functor.map_comp_apply]
  change (dgVerdierOver A D P x : SSet).map
    (SimplexCategory.const ⦋0⦌ ⦋N + 1⦌ 0).op
      ((dgVerdierOver A D P x : SSet).δ (0 : Fin (N + 2)).succ _) = _
  rw [dgVerdierConeNextSimplex_face_positive]
  exact (dgVerdierConeNextLower A D P x C τ T).first_vertex N le_rfl (K.δ 0 (τ i))

/-- 元の同じ図式面を持つ二つの次次数充填は、対応する実面も厳密に共有する。 -/
lemma dgVerdierConeNextSimplex_commonFace_eq (i j : Fin m) (k l : Fin (N + 2))
    (hface : K.δ k (τ i) = K.δ l (τ j)) :
    (dgVerdierOver A D P x : SSet).δ k.succ (dgVerdierConeNextSimplex A D P x C τ T i) =
      (dgVerdierOver A D P x : SSet).δ l.succ (dgVerdierConeNextSimplex A D P x C τ T j) := by
  rw [dgVerdierConeNextSimplex_face_positive, dgVerdierConeNextSimplex_face_positive]
  exact congrArg ((dgVerdierConeNextLower A D P x C τ T).simplex N le_rfl) hface

/-- 次次数の指定有限族は、同じ更新済み下次数錐の全面と apex を持つ実単体を同時に持つ。 -/
theorem dgVerdierConeNextFinite_exists :
    ∃ T : DGGeneralLastHornFiniteRefinement P (dgVerdierSimplexSource A D P x C.apex)
        (fun i => dgVerdierBoundaryHorn A D P x (truncatedConeNextBoundary C (τ i))),
      ∀ i, ∃ U : (dgVerdierOver A D P x : SSet) _⦋N + 2⦌,
        (dgVerdierOver A D P x : SSet).δ 0 U = f.app _ (τ i) ∧
        (∀ k : Fin (N + 2), (dgVerdierOver A D P x : SSet).δ k.succ U =
          (dgVerdierConeNextLower A D P x C τ T).simplex N le_rfl (K.δ k (τ i))) ∧
        (dgVerdierOver A D P x : SSet).map (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op U =
          (dgVerdierConeNextLower A D P x C τ T).apex := by
  obtain ⟨T⟩ := dgVerdierConeNextFiniteRefinement_nonempty A D P x C τ
  exact ⟨T, fun i => ⟨dgVerdierConeNextSimplex A D P x C τ T i,
    dgVerdierConeNextSimplex_face_zero A D P x C τ T i,
    dgVerdierConeNextSimplex_face_positive A D P x C τ T i,
    dgVerdierConeNextSimplex_first_vertex A D P x C τ T i⟩⟩

end SerrePositivity.InfinityCategories
