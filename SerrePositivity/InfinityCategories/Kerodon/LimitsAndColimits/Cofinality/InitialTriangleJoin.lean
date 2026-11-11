module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InitialHornJoin

/-!
概要：三角形の最初のホーンと境界の pushout-join を高次元の最初のホーンとして表示する。
方針：標準単体の join 同型によるホーンの逆像の公式を左次元二で使う。
規約：指定する辺は三角形の 0→1 の辺。
使われ方：cocartesian 辺の三角形に沿う消去の相対的な余錐充填。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：三角形と標準単体の join を次数 n+3 の標準単体として表す。
方針：joinStdSimplexIso の次数を正規化する。
規約：左因子は Δ²。
使われ方：三角形の余錐の外側ホーンへの移送。 -/
def initialTriangleJoinIso (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2] : SSet.{u}) Δ[n] ≅ Δ[n + 3] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 n ≪≫ eqToIso
    (congrArg (fun d : ℕ ↦ (Δ[d] : SSet.{u})) (show 2 + n + 1 = n + 3 by omega))

/-- 概要：最初のホーンの逆像は左の最初のホーンと右境界の和。
方針：一般のホーンと境界の逆像の公式を使う。
規約：右の境界が空になる n=0 も含む。
使われ方：相対的な三角形の余錐の充填。 -/
lemma initialTriangleHornJoin_preimage (n : ℕ) :
    (horn (n + 3) 0).preimage (initialTriangleJoinIso.{u} n).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 2 0) (boundary n) := by
  unfold initialTriangleJoinIso
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.initialHorn_preimage_eqToIso (show 2 + n + 1 = n + 3 by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 n)]
  convert _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.horn_boundary_preimage.{u} 1 n (0 : Fin 3) using 2
  congr 1

/-- 概要：三角形の最初のホーンと右境界の和は高次元の最初のホーンと同型。
方針：逆像の表示と部分複体の逆像同型を合成する。
規約：同型は pushout-join からホーンへ向かう。
使われ方：cocartesian 性による指定辺を持つ充填。 -/
def initialTriangleHornJoinIso (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 2 0) (boundary n) : SSet.{u}) ≅ horn (n + 3) 0 :=
  Subcomplex.eqToIso (initialTriangleHornJoin_preimage n).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso _ (initialTriangleJoinIso n)

/-- 概要：ホーン同型は周囲の標準単体への包含と可換。
方針：逆像同型の包含の式を使う。
規約：標準単体の次数は n+3。
使われ方：底の図式を厳密に保つ充填。 -/
lemma initialTriangleHornJoinIso_hom_ι (n : ℕ) :
    (initialTriangleHornJoinIso.{u} n).hom ≫ (horn (n + 3) 0).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 2 0) (boundary n)).ι ≫ (initialTriangleJoinIso n).hom := by
  change (Subcomplex.homOfLE (initialTriangleHornJoin_preimage n).symm.le ≫
    (horn (n + 3) 0).fromPreimage (initialTriangleJoinIso n).hom) ≫ _ = _
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.homOfLE_ι]

/-- 概要：左三角形の最初の辺は全 join の最初の辺になる。
方針：二頂点で左区間の連結写像を計算する。
規約：三角形の最初の辺は δ₂ で指定する。
使われ方：外側ホーンに指定した cocartesian 辺を移す。 -/
lemma initialTriangleJoinIso_inl_edge (n : ℕ) :
    SSet.yonedaEquiv ((stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[2] : SSet.{u}) Δ[n] ≫ (initialTriangleJoinIso n).hom) =
        stdSimplex.edge (n + 3) 0 1 (Fin.zero_le _) := by
  have hraw : SSet.yonedaEquiv ((stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[2] : SSet.{u}) Δ[n] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 2 n).hom) =
      stdSimplex.edge (2 + n + 1) 0 1 (Fin.zero_le _) := by
    apply stdSimplex.ext
    intro i
    fin_cases i
    all_goals
      apply Fin.ext
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := 3) (q := n + 1) (r := 2) 2 (by omega)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} 2 2 (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} n 0 PUnit.unit) _).val = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ (by omega)]
      rfl
  rw [← Category.assoc] at hraw
  rw [initialTriangleJoinIso, Iso.trans_hom, ← Category.assoc,
    ← Category.assoc, SSet.yonedaEquiv_comp, hraw,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.initialEdge_eqToIso (show 2 + n + 1 = n + 3 by omega)]

/-- 概要：ホーン同型は三角形の最初の辺をホーンの指定辺へ移す。
方針：周囲の単体集合への包含の後で比較する。
規約：右因子の境界の次元に依存しない。
使われ方：cocartesian 性の適用の辺条件。 -/
lemma initialTriangleHornJoinIso_edge (n : ℕ) :
    SSet.yonedaEquiv ((stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[2] : SSet.{u}) (boundary n : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (horn 2 0) (boundary n) ≫ (initialTriangleHornJoinIso n).hom) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge (n + 1) := by
  apply Subtype.ext
  change SSet.yonedaEquiv (((stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[2] : SSet.{u}) (boundary n : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (horn 2 0) (boundary n) ≫ (initialTriangleHornJoinIso n).hom) ≫
    (horn (n + 3) 0).ι) = _
  rw [Category.assoc, Category.assoc, Category.assoc,
    initialTriangleHornJoinIso_hom_ι,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight _ _) _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
  exact initialTriangleJoinIso_inl_edge n

/-- 概要：ホーン同型の逆射も周囲への包含と可換。
方針：順方向の等式を逆同型で移す。
規約：右辺は全 join の逆同型。
使われ方：元の底の図式を保つ充填への復帰。 -/
lemma initialTriangleHornJoinIso_inv_ι (n : ℕ) :
    (initialTriangleHornJoinIso.{u} n).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 2 0) (boundary n)).ι =
      (horn (n + 3) 0).ι ≫ (initialTriangleJoinIso n).inv := by
  apply (cancel_epi (initialTriangleHornJoinIso n).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
    initialTriangleHornJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
