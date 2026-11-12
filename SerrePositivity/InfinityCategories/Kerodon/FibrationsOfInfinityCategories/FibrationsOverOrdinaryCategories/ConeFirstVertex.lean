module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalLifting

/-!
概要：左に点を付けた join の右因子の外の単体の最初の頂点。
方針：join の切断が零なら右因子から来て、正なら最初の頂点は左の点に属する。
規約：非退化性は仮定しない。
使われ方：Kerodon §5.3.7（Tag 01US） の錐の制限の外側ホーンの充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：点と K の join の右因子から来ない単体の最初の頂点は錐の頂点。
方針：切断零を右包含の像として除外し、正の切断の零頂点への逆像を計算する。
規約：全次元の単体を扱う。
使われ方：Kerodon §5.3.7（Tag 01US） の相対骨格のセルの最初の頂点。 -/
lemma coneSimplex_firstVertex_of_not_range {K : SSet.{u}} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) _⦋n⦌)
    (hs : s ∉ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
  rcases s with ⟨⟨ℓ, hℓ⟩, l, r⟩
  cases ℓ with
  | zero =>
    cases l
    exact False.elim (hs ⟨r, rfl⟩)
  | succ ℓ =>
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).toOrderHom (ℓ + 1) = 1 := by
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut
      simp
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap (Δ[0] : SSet.{u}) K
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).toOrderHom ⟨⟨ℓ + 1, hℓ⟩, l, r⟩ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (Fin.ext hc)
    · apply stdSimplex.ext
      intro j
      exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    · change _ = PUnit.unit
      exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
