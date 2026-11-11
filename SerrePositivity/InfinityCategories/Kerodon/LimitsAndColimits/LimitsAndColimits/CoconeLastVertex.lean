module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-! # 余錐の基底の外の単体の終点

概要：K⋆Δ[0] の基底 K から来ない単体は、最後の頂点が余錐の頂点に一致する。
方針：join の切断が全体のときを除き、最後の頂点は右の点に属することを使う。
規約：非退化性は仮定しない。使われ方：余錐の制限射の相対的なホーン充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：点を後置した join の基底から来ない単体の終点は余錐の頂点。
方針：全体の切断を左包含の像として除外し、最後の頂点の切断が零となることを使う。
規約：全次元で成り立つ。使われ方：相対骨格のセルの最後の頂点の識別。 -/
lemma coconeSimplex_lastVertex_of_not_range {K : SSet.{u}} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋n⦌)
    (hs : s ∉ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})).app (Opposite.op ⦋n⦌))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op s =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
  rcases s with ⟨⟨ℓ, hℓ⟩, l, r⟩
  change ℓ < n + 2 at hℓ
  have hl : ℓ ≤ n := by
    by_contra h
    have he : ℓ = n + 1 := by omega
    subst ℓ
    apply hs
    refine ⟨l, ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl l = (⟨⟨n + 1, hℓ⟩, l, r⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex K Δ[0] n)
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (Fin.ext (by rfl))
    · rfl
    · have : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[0] : SSet.{u}) (n + 1 - (n + 1))) := by
        rw [Nat.sub_self]
        change Subsingleton PUnit
        infer_instance
      exact Subsingleton.elim _ _
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).toOrderHom ℓ = 0 := by
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut, show ¬n < ℓ by omega]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap K (Δ[0] : SSet.{u})
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).toOrderHom ⟨⟨ℓ, hℓ⟩, l, r⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (Fin.ext hc)
  · change _ = PUnit.unit
    exact Subsingleton.elim _ _
  · apply stdSimplex.ext
    intro j
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
