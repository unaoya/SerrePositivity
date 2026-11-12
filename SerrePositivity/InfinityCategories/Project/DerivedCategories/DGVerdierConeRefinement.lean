module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierConeRefinementEquations

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

/-- 同じ一つの追加実分母で全次数を同時に更新した、同じ図式上の実錐データ。 -/
def dgVerdierTruncatedConeRefinement : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N where
  apex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedApex A D P x C q s hs
  simplex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex A D P x C q s hs
  face_zero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex_face_zero A D P x C q s hs
  first_vertex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex_first_vertex A D P x C q s hs
  face_positive := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex_face_positive A D P x C q s hs
  degeneracy_positive := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedSimplex_degeneracy_positive A D P x C q s hs

/-- 同時更新後の実 apex の元の始対象は、追加実閉分母の始対象 q。 -/
lemma dgVerdierTruncatedConeRefinement_apex_source :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource A D P x
      (dgVerdierTruncatedConeRefinement A D P x C q s hs).apex = q := by
  unfold dgVerdierTruncatedConeRefinement _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeRefinedApex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialMap, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_obj_zero A D _ q s

/-- 同時更新後の全錐単体の元の始対象は、同じ一つの追加実閉分母の始対象 q。 -/
lemma dgVerdierTruncatedConeRefinement_simplex_source (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource A D P x
      ((dgVerdierTruncatedConeRefinement A D P x C q s hs).simplex n hn σ) = q :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeSimplex_source A D P x (dgVerdierTruncatedConeRefinement A D P x C q s hs)
    n hn σ).trans (dgVerdierTruncatedConeRefinement_apex_source A D P x C q s hs)

/-- 同じ錐の低次数への制限と、一つの追加実分母による同時更新は可換。 -/
lemma dgVerdierTruncatedConeRefinement_restrict (M : ℕ) (hMN : M ≤ N) :
    (dgVerdierTruncatedConeRefinement A D P x C q s hs).restrict M hMN =
      dgVerdierTruncatedConeRefinement A D P x (C.restrict M hMN) q s hs := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
