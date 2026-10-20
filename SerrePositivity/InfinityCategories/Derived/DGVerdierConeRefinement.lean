module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierConeRefinementEquations

/-! # 一つの追加実分母による有限次数錐データ全体の更新

概要：同じ図式上の全実単体・apex・面・退化条件を、一つの閉細分で同時に更新する。
方針：全整合式を同じ有限次数錐のフィールドへ束ねる。
規約：既存次数全体を更新し図式は固定。使われ方：次次数の有限同時充填への前処理。
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

/-- 同じ一つの追加実分母で全次数を同時に更新した、同じ図式上の実錐データ。 -/
def dgVerdierTruncatedConeRefinement : TruncatedJoinConeData f N where
  apex := dgVerdierConeRefinedApex A D P x C q s hs
  simplex := dgVerdierConeRefinedSimplex A D P x C q s hs
  face_zero := dgVerdierConeRefinedSimplex_face_zero A D P x C q s hs
  first_vertex := dgVerdierConeRefinedSimplex_first_vertex A D P x C q s hs
  face_positive := dgVerdierConeRefinedSimplex_face_positive A D P x C q s hs
  degeneracy_positive := dgVerdierConeRefinedSimplex_degeneracy_positive A D P x C q s hs

/-- 同時更新後の実 apex の元の始対象は、追加実閉分母の始対象 q。 -/
lemma dgVerdierTruncatedConeRefinement_apex_source :
    dgVerdierSimplexSource A D P x
      (dgVerdierTruncatedConeRefinement A D P x C q s hs).apex = q := by
  unfold dgVerdierTruncatedConeRefinement dgVerdierConeRefinedApex dgVerdierSimplexSource
  rw [dgVerdierSimplexInitialRefinement_val, dgOverSimplexInitialRefinement_simplex,
    dgOverSimplexInitialMap, Equiv.apply_symm_apply]
  exact dgSimplexInitialRefinement_obj_zero A D _ q s

/-- 同時更新後の全錐単体の元の始対象は、同じ一つの追加実閉分母の始対象 q。 -/
lemma dgVerdierTruncatedConeRefinement_simplex_source (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    dgVerdierSimplexSource A D P x
      ((dgVerdierTruncatedConeRefinement A D P x C q s hs).simplex n hn σ) = q :=
  (dgVerdierConeSimplex_source A D P x (dgVerdierTruncatedConeRefinement A D P x C q s hs)
    n hn σ).trans (dgVerdierTruncatedConeRefinement_apex_source A D P x C q s hs)

/-- 同じ錐の低次数への制限と、一つの追加実分母による同時更新は可換。 -/
lemma dgVerdierTruncatedConeRefinement_restrict (M : ℕ) (hMN : M ≤ N) :
    (dgVerdierTruncatedConeRefinement A D P x C q s hs).restrict M hMN =
      dgVerdierTruncatedConeRefinement A D P x (C.restrict M hMN) q s hs := rfl

end SerrePositivity.InfinityCategories
