module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityFibrations
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityLocalization
public import SerrePositivity.KST.Comparison.KanBasePullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 任意の基底での Kan fibration に沿う局所化同型の引き戻し

概要：基底の Kan 性なしに、Kan fibration に沿う局所化同型の引き戻しの可逆性を証明する。
方針：有限極限と Kan fibration を保つ Ex∞ で Kan 基底へ送り、単位の局所化同型で戻す。
規約：Moss arXiv:1506.04887v2 §5 冒頭の Ex∞ による right properness の経路。
使われ方：Segal 1974 Proposition 1.6 の任意の基底でのホモトピー引き戻し比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：任意の基底上の Kan fibration に沿う局所化同型の引き戻しは局所化同型である。
方針：Ex∞ が引き戻しと Kan fibration を保つことを使い、Kan 基底上の結果を適用する。
規約：モデル構造や基底の Kan 性を追加で仮定しない。
使われ方：ホモトピー引き戻しの任意の基底での不変性。
-/
@[kerodon 0104]
theorem pullback_localized_isIso {A B E P : SSet.{u}}
    (i : A ⟶ B) (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
    (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (j : P ⟶ E) (k : P ⟶ A) (sq : IsPullback j k p i) :
    IsIso (AnodyneHomotopy.anodyneQ.map j) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff j).mp
  exact pullback_localized_isIso_of_kan_base (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map i)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff i).mpr hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_rlp p hp) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map j) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map k) (sq.map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity)

/--
概要：任意の基底のスライスで、Kan fibration との積は局所化同型を保つ。
方針：誘導写像の引き戻し正方形に、任意の基底の引き戻しの結果を適用する。
規約：基底 B の Kan 性は要求しない。
使われ方：任意の基底でのホモトピー引き戻し模型の比較。
-/
theorem sliceFiberFunctor_localized_isIso_anyBase {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {X Y : Over B} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.left)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor p).map f)) := by
  exact pullback_localized_isIso f.left hf (pullback.fst Y.hom p)
    (SSet.modelCategoryQuillen.J.rlp.pullback_fst Y.hom p hp)
    ((sliceFiberFunctor p).map f) (pullback.fst X.hom p) (sliceFiberFunctor_map_isPullback p f)

end SerrePositivity.KST.Comparison
