module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteJoinCover
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteJoinPieces

/-!
概要：有限単体集合どうしの join は有限である。
方針：有限個の非退化単体の対による有限な標準 join の像で被覆する。
規約：各次数の有限性だけでなく非退化単体全体の有限性を証明する。
使われ方：filtered ∞ 圏の有限図式の下の coslice の filtered 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：有限な両因子から作る被覆の各部品は有限。
方針：元の因子の像と標準単体の join の像の有限性を使う。
規約：標準単体の join は既存の同型で標準単体へ戻す。
使われ方：有限個の部品の上限による有限性。 -/
lemma finite_finiteJoinPiece (K L : SSet.{u}) [K.Finite] [L.Finite]
    (i : Unit ⊕ Unit ⊕ (K.N × L.N)) : SSet.Finite (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteJoinPiece K L i : SSet.{u}) := by
  rcases i with _ | (_ | ⟨a, b⟩)
  · exact SSet.finite_range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L)
  · exact SSet.finite_range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L)
  · have : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[a.dim] : SSet.{u}) Δ[b.dim]).Finite :=
      SSet.finite_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso a.dim b.dim).symm
    exact SSet.finite_range _

/-- 概要：有限単体集合の join の非退化単体は有限個である。
方針：両因子と非退化単体の対の像による有限被覆に有限性の判定を適用する。
規約：有限な全ての単体集合を扱う。
使われ方：coslice の filtered 性の試験形状。 -/
instance finite_join (K L : SSet.{u}) [K.Finite] [L.Finite] : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).Finite := by
  rw [← SSet.finite_subcomplex_top_iff, ← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.iSup_finiteJoinPiece K L, SSet.finite_iSup_iff]
  exact finite_finiteJoinPiece K L

end SerrePositivity.InfinityCategories.Project.FilteredExchange
