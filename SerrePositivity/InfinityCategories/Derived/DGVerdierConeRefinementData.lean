module
public import SerrePositivity.InfinityCategories.Derived.TruncatedJoinConeData
public import SerrePositivity.InfinityCategories.Derived.DGVerdierInitialRefinementNaturality

/-! # 有限次数の実分母錐の共通追加射と同じ閉細分データ

概要：全錐単体の始対象を同じ apex の始対象へ揃え、一つの追加実閉分母を全次数へ渡す。
方針：始頂点の等式から対象を同定し、終対象の等式輸送で同じ追加実辺を保持する。
規約：既存錐の全単体を同時に扱う。使われ方：次数帰納で下次数の錐全体を更新する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (P : Set D) (x : D)

/-- 実分母 over 単体の、元の dg 圏での始対象。 -/
def dgVerdierSimplexSource {n : ℕ}
    (σ : (dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌) : D :=
  (SSet.yonedaEquiv (roofPointSliceSimplex _ σ.val)).obj 0

variable {K : SSet.{max u v}} {f : K ⟶ (dgVerdierOver A D P x : SSet)} {N : ℕ}
variable (C : TruncatedJoinConeData f N)

/-- 全次数の錐単体の元の始対象は、同じ apex の始対象である。 -/
lemma dgVerdierConeSimplex_source (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    dgVerdierSimplexSource A D P x (C.simplex n hn σ) =
      dgVerdierSimplexSource A D P x C.apex :=
  (dgOverSimplexReindex_source _ (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)
    (C.simplex n hn σ).val rfl).trans
      (congrArg (dgVerdierSimplexSource A D P x) (C.first_vertex n hn σ))

variable (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) (dgVerdierSimplexSource A D P x C.apex))

/-- 共通追加閉射を、各錐単体の同じ始対象へ型だけ輸送した射。 -/
def dgVerdierConeRefinementMap (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    ForgetEnrichment.of (Complex A) q ⟶
      ForgetEnrichment.of (Complex A) (dgVerdierSimplexSource A D P x (C.simplex n hn σ)) :=
  dgClosedTargetTransport A D s (dgVerdierConeSimplex_source A D P x C n hn σ).symm

/-- 全次数へ輸送した追加閉射の実辺は、元の同じ一つの実辺。 -/
lemma dgVerdierConeRefinementMap_edge (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    (dgClosedEdge A D (dgVerdierConeRefinementMap A D P x C q s n hn σ)).edge =
      (dgClosedEdge A D s).edge :=
  dgClosedTargetTransport_edge A D s _

variable [Small.{u} D] [IsDGPretriangulated A D]
variable (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)

/-- 一つの追加実分母で細分した、新しい同じ共通 apex。 -/
def dgVerdierConeRefinedApex : (dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  dgVerdierSimplexInitialRefinement A D P x C.apex q s hs

/-- 同じ一つの追加実分母で同時に細分した、全次数の実錐単体。 -/
def dgVerdierConeRefinedSimplex (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    (dgVerdierOver A D P x : SSet) _⦋n + 1⦌ :=
  dgVerdierSimplexInitialRefinement A D P x (C.simplex n hn σ) q
    (dgVerdierConeRefinementMap A D P x C q s n hn σ)
    (dgClosedTargetTransport_mem A D P s _ hs)

end SerrePositivity.InfinityCategories
