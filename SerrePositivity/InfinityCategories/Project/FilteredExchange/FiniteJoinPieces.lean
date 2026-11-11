module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：join を両因子と非退化単体の対からの標準 join の像で被覆するための部品。
方針：各単体を非退化単体の引き戻しとして表示し、標準単体からの射で表す。
規約：空の片側は因子そのものの像として別に含める。
使われ方：有限な形状の join の有限性と filtered な coslice。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：任意の単体はある非退化単体からの標準単体射の像に属する。
方針：非退化分解の単体作用素を標準単体の単体として用いる。
規約：因子の有限性は不要。使われ方：join の両因子の有限個の生成元への分解。 -/
lemma simplex_in_nondegenerate_range {K : SSet.{u}} {n : ℕ} (x : K _⦋n⦌) :
    ∃ a : K.N, ∃ y : (Δ[a.dim] : SSet.{u}) _⦋n⦌,
      (SSet.yonedaEquiv.symm a.simplex).app (Opposite.op ⦋n⦌) y = x := by
  obtain ⟨m, f, _, y, hx⟩ := K.exists_nonDegenerate x
  refine ⟨SSet.N.mk y.val y.property, stdSimplex.objEquiv.symm f, ?_⟩
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
  exact hx.symm

/-- 概要：二因子と非退化単体の対で添字付けた join の部分複体。
方針：二つの包含の像と標準単体の join からの像を並べる。
規約：添字の Unit は空の片側に対応する。
使われ方：有限個の有限部分複体による join の被覆。 -/
def finiteJoinPiece (K L : SSet.{u}) : Unit ⊕ Unit ⊕ (K.N × L.N) → (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).Subcomplex
  | .inl _ => Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L)
  | .inr (.inl _) => Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L)
  | .inr (.inr (a, b)) => Subcomplex.range
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a.simplex) (SSet.yonedaEquiv.symm b.simplex))

end SerrePositivity.InfinityCategories.Project.FilteredExchange
