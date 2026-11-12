module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteJoinPieces

/-!
概要：任意の join を非退化単体で添字付けた有限部分複体で覆う。
方針：片側だけの部品も標準単体の像へ細分する。
規約：両因子の有限性を仮定しない。
使われ方：正則 κ に対する κ-small join の濃度評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：join の非退化単体で添字付けた有限な部品。
方針：片側の標準単体の像と、標準単体どうしの join の像を並べる。
規約：空の片側も非退化単体で添字付ける。使われ方：κ-small な有限被覆。 -/
def smallJoinPiece (K L : SSet.{u}) : K.N ⊕ L.N ⊕ (K.N × L.N) → (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).Subcomplex
  | .inl a => Subcomplex.range (SSet.yonedaEquiv.symm a.simplex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L)
  | .inr (.inl b) => Subcomplex.range (SSet.yonedaEquiv.symm b.simplex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L)
  | .inr (.inr (a, b)) => _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteJoinPiece K L (.inr (.inr (a, b)))

/-- 概要：小さい join の被覆の各部品は有限。
方針：標準単体の有限性とその有限 join の有限性を像に移す。
規約：元の両因子は任意。使われ方：部品の κ-small 性。 -/
instance finite_smallJoinPiece (K L : SSet.{u})
    (i : K.N ⊕ L.N ⊕ (K.N × L.N)) : SSet.Finite (smallJoinPiece K L i : SSet.{u}) := by
  rcases i with a | (b | ⟨a, b⟩)
  · exact SSet.finite_range _
  · exact SSet.finite_range _
  · have : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[a.dim] : SSet.{u}) Δ[b.dim]).Finite :=
      SSet.finite_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso a.dim b.dim).symm
    exact SSet.finite_range _

/-- 概要：左右の頂点数で表示した単体はいずれかの有限な部品に属する。
方針：非空の各成分を非退化単体からの像として表す。
規約：片側が空の単体も含む。使われ方：join 全体の有限な部品による被覆。 -/
lemma mkOfSum_mem_smallJoinPiece {K L : SSet.{u}} {n l r : ℕ}
    (h : l + r = n + 1) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L r) :
    ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h a b ∈ (smallJoinPiece K L i).obj (Opposite.op ⦋n⦌) := by
  cases l with
  | zero =>
    have hr : r = n + 1 := by omega
    subst r
    obtain ⟨lb, y, hy⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.simplex_in_nondegenerate_range (K := L) b
    refine ⟨.inr (.inl lb), y, ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum (K := K) (L := L) (l := 0) (r := n + 1) (by omega) PUnit.unit
      ((SSet.yonedaEquiv.symm lb.simplex).app _ y) = _
    rw [hy]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext <;> try rfl
  | succ l =>
    cases r with
    | zero =>
      have hl : l = n := by omega
      subst l
      obtain ⟨ka, x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.simplex_in_nondegenerate_range (K := K) a
      refine ⟨.inl ka, x, ?_⟩
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum (K := K) (L := L) (l := n + 1) (r := 0) (by omega)
        ((SSet.yonedaEquiv.symm ka.simplex).app _ x) PUnit.unit = _
      simp only [hx, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_zero_right]
    | succ r =>
      obtain ⟨ka, x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.simplex_in_nondegenerate_range (K := K) a
      obtain ⟨lb, y, hy⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.simplex_in_nondegenerate_range (K := L) b
      refine ⟨.inr (.inr (ka, lb)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h x y, ?_⟩
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mkOfSum]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h ((SSet.yonedaEquiv.symm ka.simplex).app _ x)
        ((SSet.yonedaEquiv.symm lb.simplex).app _ y) = _
      rw [hx, hy]

/-- 概要：非退化単体で添字付けた有限な部品の上限は join 全体。
方針：任意の単体を左右の頂点数による表示へ戻す。
規約：両因子は任意。使われ方：上限の濃度評価の適用。 -/
lemma iSup_smallJoinPiece (K L : SSet.{u}) : ⨆ i, smallJoinPiece K L i = ⊤ := by
  apply le_antisymm le_top
  intro n s _
  obtain ⟨⟨n⟩⟩ := n
  obtain ⟨i, hi⟩ := mkOfSum_mem_smallJoinPiece (K := K) (L := L) (n := n)
    (by
      change s.1.val + (n + 1 - s.1.val) = n + 1
      have hs : s.1.val < n + 2 := s.1.isLt
      omega) s.2.1 s.2.2
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_eta] at hi
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨i, hi⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
