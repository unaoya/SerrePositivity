module

public import SerrePositivity.KST.Fibration.RelativeFirstRowSimplexQuotient
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorPullbackSquares
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableFiniteLimitsColimits

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

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の標準単体上の core 逆像は、同じ全頂点評価による相対図式そのもの。 -/
lemma relativeFirstRowSimplex_eq_relativeDiagram (n : ℕ) :
    relativeFirstRowSimplex q n =
      relativeDiagram q.hom (fun k : (Δ[n] : SSet.{u}) _⦋0⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) := by
  simpa only [relativeFirstRowSimplex, Category.id_comp] using
    (relativeDiagram_eq_functorCore_preimage q.hom
      (𝟙 ((ihom (Δ[n] : SSet.{u})).obj B.obj))).symm

/-- 全高次単体の条件を、元の有限図式の全頂点と全一次制限で判定する。 -/
lemma relativeFirstRowSimplex_mem_iff (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)
    {m : SimplexCategoryᵒᵖ} (s : ((ihom (Δ[n] : SSet.{u})).obj B.obj).obj m) :
    s ∈ (relativeFirstRowSimplex q n).obj m ↔
      ∀ k : (Δ[n] : SSet.{u}) _⦋0⦌, ∀ α : ⦋1⦌ ⟶ m.unop,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋1⦌)
          (((ihom (Δ[n] : SSet.{u})).obj B.obj).map α.op s) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  rw [relativeFirstRowSimplex_eq_relativeDiagram]
  exact relativeDiagram_mem_iff h _ s

/-- 元の標準単体図式の辺の所属は、全頂点での同じ Verdier 分母の所属。 -/
lemma relativeFirstRowSimplex_mem_edge_iff (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)
    (s : ((ihom (Δ[n] : SSet.{u})).obj B.obj) _⦋1⦌) :
    s ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ↔
      ∀ k : (Δ[n] : SSet.{u}) _⦋0⦌,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋1⦌) s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  rw [relativeFirstRowSimplex_eq_relativeDiagram]
  exact relativeDiagram_mem_edge_iff h _ s

/-- 元の core 逆像の始域は、全高次図式を持つ quasicategory。 -/
instance relativeFirstRowSimplex_quasicategory (n : ℕ) :
    Quasicategory (relativeFirstRowSimplex q n : SSet.{u}) := by
  rw [relativeFirstRowSimplex_eq_relativeDiagram]
  infer_instance

/-- 元の有限図式の実引き戻しの両縦辺は、同じ分母条件を保ち反映する。 -/
lemma relativeFirstRowSimplex_pullback_iff (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj)
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow Q).edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ↔
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow Q).edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits B.obj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable B.obj
  rw [relativeFirstRowSimplex_mem_edge_iff h, relativeFirstRowSimplex_mem_edge_iff h]
  apply forall_congr'
  intro k
  have hk := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff Q).mp hQ k
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pullback_iff h (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) hk

/-- 同じ標準単体上の任意の二辺を、全図式を保つ実引き戻しへ完成する。
右辺が元の分母なら左辺も元の同じ core 逆像に属する。 -/
lemma relativeFirstRowSimplex_exists_pullback (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)
    (d : (horn 2 2 : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj)
    (hd : SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ d) ∈
      (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q = d ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q ∧
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow Q).edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits B.obj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable B.obj
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom (Δ[n] : SSet.{u})).obj B.obj) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory _ _
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit d
  let Q := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c
  have hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback c hc
  have hQd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q = d := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_cospan c
  refine ⟨Q, hQd, hQ, (relativeFirstRowSimplex_pullback_iff h n Q hQ).mpr ?_⟩
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = horn₂₂.ι₀₂ ≫ d := by
    rw [← hQd, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow Q).edge ∈
    (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge, hr]
  exact hd

end SerrePositivity.KST.LocalizingInvariants
