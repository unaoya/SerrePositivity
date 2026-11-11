module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeLastFaceRecovery
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone

/-!
概要：右錐の単体は元の左単体か、最後の頂点が右頂点となる単体に分かれる。
方針：切断が全頂点数と一致する場合を分け、既存の頂点の切断判定を使う。
規約：元の単体と頂点の等式を用い、非退化性は仮定しない。
使われ方：元の図式と新しい終頂点への余錐を同じ実現空間に貼り合わせる。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K : SSet.{u}}

/-- 切断が全頂点を含めば、同じ単体は左因子から来る。 -/
lemma coneSimplex_inl_of_cut {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋n⦌)
    (hs : s.1.val = n + 1) : ∃ x : K _⦋n⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ x = s := by
  rcases s with ⟨⟨r, hr⟩, x, y⟩
  change r = n + 1 at hs
  subst r
  refine ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (Fin.ext rfl) ?_ ?_⟩
  · rfl
  · exact Subsingleton.elim _ _

/-- 全ての単体は左因子から来るか、最後の頂点が同じ右頂点に一致する。 -/
lemma coneSimplex_inl_or_last_apex {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋n⦌) :
    (∃ x : K _⦋n⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ x = s) ∨
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex s (Fin.last n) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K := by
  by_cases hs : s.1.val = n + 1
  · exact Or.inl (coneSimplex_inl_of_cut s hs)
  · apply Or.inr
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex_eq_apex_iff _ _).mpr
    have hl : s.1.val < n + 2 := s.1.isLt
    change s.1.val ≤ n
    omega

/-- 余錐の元の頂点は、同じ写像による右頂点の像。 -/
lemma joinCocone_vertex_eq_map_apex {X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    c.vertex = c.val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  have he : SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) = stdSimplex.obj₀Equiv.symm 0 := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  change c.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]).app _ (SSet.yonedaEquiv (𝟙 Δ[0]))) = _
  rw [he]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
