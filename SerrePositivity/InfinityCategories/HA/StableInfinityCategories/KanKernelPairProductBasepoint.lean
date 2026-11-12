module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairBasepoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairLoopProduct

/-! # 自己引き戻しのループ積の基点独立性

概要：可縮な全空間の自己引き戻しの π₀ 上のループ積は、全空間の基点の選択に依存しない。
方針：二つのループ表示の共役公式と射の合成の保存を使い、可逆な基点間の像を消去する。
規約：比較同値自体は基点で変わるが、移した二項演算は等しい。使われ方：Hom 上の自然な演算の確定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：自己引き戻しの連結成分に移したループ積は基点の選択に依存しない。
方針：基点を結ぶ辺を可縮性で選び、共役の合成保存を二つの入力と積に適用する。
規約：r は Kan fibration、E は可縮な Kan、B も Kan。使われ方：終域の基点を自由に選ぶ自然性。 -/
lemma kanKernelPairLoopProduct_basepoint {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e d : E _⦋0⦌)
    (b c : SSet.π₀ (pullback r r)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct r hE e b c = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct r hE d b c := by
  obtain ⟨a⟩ := (hE.isInitialVertex e).nonempty_edge d
  let β := SSet.Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map r))
  have : IsIso β := IsGroupoid.all_isIso (C := hoFunctor.obj B) β
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE d).injective
  apply (cancel_epi β).1
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_basepoint r hE a (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct r hE e b c),
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_product, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_product]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_basepoint r hE a c,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_basepoint r hE a b, Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
