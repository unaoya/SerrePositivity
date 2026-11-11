module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells

/-!
概要：最後の外側ホーンの境界と辺の join による表示。
方針：A2c の境界とホーンの逆像の計算を一次ホーンに適用する。
規約：Δ[n]⋆Δ[1]≅Δ[n+2]、右のホーンは最後の頂点だけ。
使われ方：Kerodon Proposition 4.4.2.13（Tag 01H0）、HTT Proposition 1.2.4.3。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：最後の外側ホーンの join 同型による逆像。
方針：境界とホーンの一般の計算の添字を正規化する。
規約：右の一次ホーンは Λ[1,1]。
使われ方：Kerodon Proposition 4.4.2.13（Tag 01H0） の pushout の表示。 -/
lemma finalHornJoin_preimage (n : ℕ) :
    (horn (n + 2) (Fin.last (n + 2))).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n 1).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary n) (horn 1 1) := by
  convert _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.boundary_horn_preimage.{u} n 0 (1 : Fin 2) using 2
  congr 1

/-- 概要：最後の外側ホーンは境界と最後の頂点に沿う pushout-join と同型。
方針：逆像の等式と部分複体の逆像の同型を合成する。
規約：n=0 も含み、二次ホーンに適用できる。
使われ方：Kerodon Proposition 4.4.2.13（Tag 01H0） の三角形から高次元への移行。 -/
def finalHornJoinIso (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary n) (horn 1 1) : SSet.{u}) ≅ horn (n + 2) (Fin.last (n + 2)) :=
  Subcomplex.eqToIso (finalHornJoin_preimage n).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1)

/-- 概要：最後の外側ホーンの join 表示は包含と整合する。
方針：逆像の同型が包含と可換であることを使う。
規約：標的の標準単体の同型は joinStdSimplexIso。
使われ方：Kerodon Proposition 4.4.2.13（Tag 01H0） の充填の移送。 -/
lemma finalHornJoinIso_hom_ι (n : ℕ) :
    (finalHornJoinIso.{u} n).hom ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary n) (horn 1 1)).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom := by
  change (Subcomplex.homOfLE (finalHornJoin_preimage n).symm.le ≫
    (horn (n + 2) (Fin.last (n + 2))).fromPreimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫ _ = _
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.homOfLE_ι]

/-- 概要：辺を右から join したときの右因子は最後の辺になる。
方針：連結写像の右区間での値を二つの頂点で計算する。
規約：任意の n、標準単体は Δ[n+2]。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の最後の辺の固定条件。 -/
lemma joinStdSimplexIso_inr_edge (n : ℕ) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) =
      stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩ (Fin.last (n + 2)) (Fin.le_last _) := by
  apply stdSimplex.ext
  intro i
  fin_cases i
  all_goals
    apply Fin.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := n + 1) (q := 2) (r := 2) 0 (by omega)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} n 0 PUnit.unit)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} 1 2 (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))) _).val = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ (by omega)]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
