module

public import SerrePositivity.KST.Fibration.RelativeFirstRowSimplexQuotient
public import SerrePositivity.InfinityCategories.Stable.FunctorPullbackSquares
public import SerrePositivity.InfinityCategories.Stable.StableFiniteLimitsColimits

/-!
概要：有限線型図式の元の core 逆像に属する分母を、実引き戻しで精密化する。
方針：全頂点の Verdier 弱同値判定と、関手圏の点ごとの引き戻しを使う。
規約：商図式の局所化や core 逆像射影の可逆性はこの工程だけでは結論しない。
使われ方：K-6 c5 の同じ標準単体商比較の分母計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- 元の標準単体上の core 逆像は、同じ全頂点評価による相対図式そのもの。 -/
lemma relativeFirstRowSimplex_eq_relativeDiagram (n : ℕ) :
    relativeFirstRowSimplex q n =
      relativeDiagram q.hom (fun k : (Δ[n] : SSet.{u}) _⦋0⦌ => evaluateFunctorAt k) := by
  simpa only [relativeFirstRowSimplex, Category.id_comp] using
    (relativeDiagram_eq_functorCore_preimage q.hom
      (𝟙 ((ihom (Δ[n] : SSet.{u})).obj B.obj))).symm

/-- 全高次単体の条件を、元の有限図式の全頂点と全一次制限で判定する。 -/
lemma relativeFirstRowSimplex_mem_iff (h : IsVerdierSequence i q) (n : ℕ)
    {m : SimplexCategoryᵒᵖ} (s : ((ihom (Δ[n] : SSet.{u})).obj B.obj).obj m) :
    s ∈ (relativeFirstRowSimplex q n).obj m ↔
      ∀ k : (Δ[n] : SSet.{u}) _⦋0⦌, ∀ α : ⦋1⦌ ⟶ m.unop,
        (evaluateFunctorAt k).app (Opposite.op ⦋1⦌)
          (((ihom (Δ[n] : SSet.{u})).obj B.obj).map α.op s) ∈ weakEquivalences i := by
  rw [relativeFirstRowSimplex_eq_relativeDiagram]
  exact relativeDiagram_mem_iff h _ s

/-- 元の標準単体図式の辺の所属は、全頂点での同じ Verdier 分母の所属。 -/
lemma relativeFirstRowSimplex_mem_edge_iff (h : IsVerdierSequence i q) (n : ℕ)
    (s : ((ihom (Δ[n] : SSet.{u})).obj B.obj) _⦋1⦌) :
    s ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ↔
      ∀ k : (Δ[n] : SSet.{u}) _⦋0⦌,
        (evaluateFunctorAt k).app (Opposite.op ⦋1⦌) s ∈ weakEquivalences i := by
  rw [relativeFirstRowSimplex_eq_relativeDiagram]
  exact relativeDiagram_mem_edge_iff h _ s

/-- 元の core 逆像の始域は、全高次図式を持つ quasicategory。 -/
instance relativeFirstRowSimplex_quasicategory (n : ℕ) :
    Quasicategory (relativeFirstRowSimplex q n : SSet.{u}) := by
  rw [relativeFirstRowSimplex_eq_relativeDiagram]
  infer_instance

/-- 元の有限図式の実引き戻しの両縦辺は、同じ分母条件を保ち反映する。 -/
lemma relativeFirstRowSimplex_pullback_iff (h : IsVerdierSequence i q) (n : ℕ)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj)
    (hQ : IsPullbackSquare Q) :
    (squareLeftArrow Q).edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ↔
      (squareRightArrow Q).edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) := by
  have : HasFiniteLimits B.obj := hasFiniteLimits_of_isStable B.obj
  rw [relativeFirstRowSimplex_mem_edge_iff h, relativeFirstRowSimplex_mem_edge_iff h]
  apply forall_congr'
  intro k
  have hk := (isPullbackSquare_functor_iff Q).mp hQ k
  exact weakEquivalences_pullback_iff h (Q ≫ evaluateFunctorAt k) hk

/-- 同じ標準単体上の任意の二辺を、全図式を保つ実引き戻しへ完成する。
右辺が元の分母なら左辺も元の同じ core 逆像に属する。 -/
lemma relativeFirstRowSimplex_exists_pullback (h : IsVerdierSequence i q) (n : ℕ)
    (d : (horn 2 2 : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj)
    (hd : SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ d) ∈
      (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj,
      pullbackCospan Q = d ∧ IsPullbackSquare Q ∧
        (squareLeftArrow Q).edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) := by
  have : HasFiniteLimits B.obj := hasFiniteLimits_of_isStable B.obj
  have : HasFiniteLimits ((ihom (Δ[n] : SSet.{u})).obj B.obj) :=
    hasFiniteLimits_functorCategory _ _
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit d
  let Q := coneSquare c
  have hQ : IsPullbackSquare Q := coneSquare_isPullback c hc
  have hQd : pullbackCospan Q = d := coneSquare_cospan c
  refine ⟨Q, hQd, hQ, (relativeFirstRowSimplex_pullback_iff h n Q hQ).mpr ?_⟩
  have hr : squareRightEdge ≫ Q = horn₂₂.ι₀₂ ≫ d := by
    rw [← hQd, pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge]
  change (squareRightArrow Q).edge ∈
    (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  rw [squareRightArrow_edge, hr]
  exact hd

end SerrePositivity.KST.LocalizingInvariants
