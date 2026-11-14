module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierConeRefinementData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverInitialRefinementCongruence

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x : D) {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)} {N : ℕ}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource A D P x C.apex))
variable (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)

/-- 全細分錐単体の零面は、同じ元の図式単体のまま。 -/
lemma dgVerdierConeRefinedSimplex_face_zero (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex A D P x C q s hs n hn σ) =
      f.app _ σ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_face_zero]
  exact C.face_zero n hn σ

/-- 全新錐単体の最初の実頂点は、同じ新しい実 apex に一致する。 -/
lemma dgVerdierConeRefinedSimplex_first_vertex (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex A D P x C q s hs n hn σ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedApex A D P x C q s hs := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedApex
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_pullback_initial A D P x _ _ rfl
    (fun (i : Fin 1) hi => (hi (Subsingleton.elim i 0)).elim)]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_congr P x (C.first_vertex n hn σ) q q
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinementMap_edge A D P x C q s n hn σ)

/-- 全新正番号面は、同じ下次数錐単体の同じ一つの閉細分。 -/
lemma dgVerdierConeRefinedSimplex_face_positive (n : ℕ) (hn : n + 1 ≤ N)
    (σ : K _⦋n + 1⦌) (i : Fin (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex A D P x C q s hs (n + 1) hn σ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex A D P x C q s hs n (by omega) (K.δ i σ) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_face_positive A D P x _ _ _ _ i.succ
    (Fin.succ_ne_zero i)]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_congr P x (C.face_positive n hn σ i) q q
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D _ _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinementMap_edge A D P x C q s (n + 1) hn σ).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinementMap_edge A D P x C q s n (by omega) (K.δ i σ)).symm)

/-- 全新正番号退化は、同じ退化図式単体の同じ一つの閉細分。 -/
lemma dgVerdierConeRefinedSimplex_degeneracy_positive (n : ℕ) (hn : n + 1 ≤ N)
    (σ : K _⦋n⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ i.succ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex A D P x C q s hs n (by omega) σ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex A D P x C q s hs (n + 1) hn (K.σ i σ) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_degeneracy_positive A D P x _ _ _ _ i.succ
    (Fin.succ_ne_zero i)]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_congr P x (C.degeneracy_positive n hn σ i) q q
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D _ _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinementMap_edge A D P x C q s n (by omega) σ).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinementMap_edge A D P x C q s (n + 1) hn (K.σ i σ)).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
