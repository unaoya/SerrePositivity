module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierConeRefinementData
public import SerrePositivity.InfinityCategories.Derived.DGOverInitialRefinementCongruence

/-! # 一つの追加実分母による錐全体の面・退化・apex の保存

概要：全次数の同時閉細分は、同じ図式上の有限次数錐の全整合条件を保つ。
方針：各面・退化への自然性と、全追加実辺が同じであることによる congruence を使う。
規約：新 apex 自体も実単体として厳密に揃える。使われ方：有限次数錐の更新操作。
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
variable (C : TruncatedJoinConeData f N) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) (dgVerdierSimplexSource A D P x C.apex))
variable (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)

/-- 全細分錐単体の零面は、同じ元の図式単体のまま。 -/
lemma dgVerdierConeRefinedSimplex_face_zero (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    (dgVerdierOver A D P x : SSet).δ 0 (dgVerdierConeRefinedSimplex A D P x C q s hs n hn σ) =
      f.app _ σ := by
  unfold dgVerdierConeRefinedSimplex
  rw [dgVerdierSimplexInitialRefinement_face_zero]
  exact C.face_zero n hn σ

/-- 全新錐単体の最初の実頂点は、同じ新しい実 apex に一致する。 -/
lemma dgVerdierConeRefinedSimplex_first_vertex (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    (dgVerdierOver A D P x : SSet).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
        (dgVerdierConeRefinedSimplex A D P x C q s hs n hn σ) =
      dgVerdierConeRefinedApex A D P x C q s hs := by
  unfold dgVerdierConeRefinedSimplex dgVerdierConeRefinedApex
  rw [dgVerdierSimplexInitialRefinement_pullback_initial A D P x _ _ rfl
    (fun (i : Fin 1) hi => (hi (Subsingleton.elim i 0)).elim)]
  apply dgVerdierSimplexInitialRefinement_congr P x (C.first_vertex n hn σ) q q
  exact (dgClosedTargetTransport_edge A D _ _).trans
    (dgVerdierConeRefinementMap_edge A D P x C q s n hn σ)

/-- 全新正番号面は、同じ下次数錐単体の同じ一つの閉細分。 -/
lemma dgVerdierConeRefinedSimplex_face_positive (n : ℕ) (hn : n + 1 ≤ N)
    (σ : K _⦋n + 1⦌) (i : Fin (n + 2)) :
    (dgVerdierOver A D P x : SSet).δ i.succ
        (dgVerdierConeRefinedSimplex A D P x C q s hs (n + 1) hn σ) =
      dgVerdierConeRefinedSimplex A D P x C q s hs n (by omega) (K.δ i σ) := by
  unfold dgVerdierConeRefinedSimplex
  rw [dgVerdierSimplexInitialRefinement_face_positive A D P x _ _ _ _ i.succ
    (Fin.succ_ne_zero i)]
  apply dgVerdierSimplexInitialRefinement_congr P x (C.face_positive n hn σ i) q q
  exact (dgClosedTargetTransport_edge A D _ _).trans
    ((dgVerdierConeRefinementMap_edge A D P x C q s (n + 1) hn σ).trans
      (dgVerdierConeRefinementMap_edge A D P x C q s n (by omega) (K.δ i σ)).symm)

/-- 全新正番号退化は、同じ退化図式単体の同じ一つの閉細分。 -/
lemma dgVerdierConeRefinedSimplex_degeneracy_positive (n : ℕ) (hn : n + 1 ≤ N)
    (σ : K _⦋n⦌) (i : Fin (n + 1)) :
    (dgVerdierOver A D P x : SSet).σ i.succ
        (dgVerdierConeRefinedSimplex A D P x C q s hs n (by omega) σ) =
      dgVerdierConeRefinedSimplex A D P x C q s hs (n + 1) hn (K.σ i σ) := by
  unfold dgVerdierConeRefinedSimplex
  rw [dgVerdierSimplexInitialRefinement_degeneracy_positive A D P x _ _ _ _ i.succ
    (Fin.succ_ne_zero i)]
  apply dgVerdierSimplexInitialRefinement_congr P x (C.degeneracy_positive n hn σ i) q q
  exact (dgClosedTargetTransport_edge A D _ _).trans
    ((dgVerdierConeRefinementMap_edge A D P x C q s n (by omega) σ).trans
      (dgVerdierConeRefinementMap_edge A D P x C q s (n + 1) hn (K.σ i σ)).symm)

end SerrePositivity.InfinityCategories
