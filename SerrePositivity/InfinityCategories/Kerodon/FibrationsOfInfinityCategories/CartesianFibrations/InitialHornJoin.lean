module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornJoin
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge

/-!
概要：最初の外側ホーンを左の一次ホーンと右の境界の pushout-join として表示する。
方針：標準単体の join の同型とホーンの逆像の公式を使う。
規約：左因子は Δ[1]、右因子は Δ[n]。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、cocartesian 辺の相対 coslice による特徴づけ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：Δ[1] と Δ[n] の join を添字 n+2 の標準単体として表示する。
方針：一般の join の同型の添字を正規化する。
規約：左因子が指定する辺は最初の辺。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、初期ホーンの添字の統一。 -/
def initialEdgeJoinIso (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) Δ[n] ≅ Δ[n + 2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 n ≪≫ eqToIso
    (congrArg (fun d : ℕ ↦ (Δ[d] : SSet.{u})) (show 1 + n + 1 = n + 2 by omega))

/-- 概要：次数の等式による標準単体の移送は最初のホーンの逆像を保つ。
方針：次数の等式を消去して恒等同型に帰着する。
規約：ホーンの添字は常に零。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、join の次数の正規化。 -/
lemma initialHorn_preimage_eqToIso {A : SSet.{u}} {m n : ℕ} (h : m = n)
    (e : A ≅ (Δ[m] : SSet.{u})) :
    (horn n 0).preimage
      (e ≪≫ eqToIso (congrArg (fun d : ℕ ↦ (Δ[d] : SSet.{u})) h)).hom =
        (horn m 0).preimage e.hom := by
  subst n
  simp

/-- 概要：最初の外側ホーンの join 同型による逆像は左ホーンと右境界の和。
方針：一般のホーンの逆像の計算を次数一の左因子に適用する。
規約：零次の右境界も含む。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、coslice の境界持ち上げとの比較。 -/
lemma initialHornJoin_preimage (n : ℕ) :
    (horn (n + 2) 0).preimage (initialEdgeJoinIso.{u} n).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 1 0) (boundary n) := by
  unfold initialEdgeJoinIso
  rw [initialHorn_preimage_eqToIso (show 1 + n + 1 = n + 2 by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 n)]
  convert _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.horn_boundary_preimage.{u} 0 n (0 : Fin 2) using 2
  congr 1

/-- 概要：最初の外側ホーンは左の一次ホーンと右境界の pushout-join と同型。
方針：逆像の等式を部分複体の逆像同型と合成する。
規約：同型は pushout-join からホーンへ向かう。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、相対 coslice の充填の移送。 -/
def initialHornJoinIso (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 1 0) (boundary n) : SSet.{u}) ≅ horn (n + 2) 0 :=
  Subcomplex.eqToIso (initialHornJoin_preimage n).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso _ (initialEdgeJoinIso n)

/-- 概要：初期ホーンの join 同型は周囲の標準単体への包含と可換。
方針：部分複体の逆像同型の包含の公式を使う。
規約：標準単体の添字は n+2 に統一する。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、底の単体を厳密に保つ充填。 -/
lemma initialHornJoinIso_hom_ι (n : ℕ) :
    (initialHornJoinIso.{u} n).hom ≫ (horn (n + 2) 0).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 1 0) (boundary n)).ι ≫ (initialEdgeJoinIso n).hom := by
  change (Subcomplex.homOfLE (initialHornJoin_preimage n).symm.le ≫
    (horn (n + 2) 0).fromPreimage (initialEdgeJoinIso n).hom) ≫ _ = _
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.homOfLE_ι]

/-- 概要：次数の等式で標準単体を移送しても最初の辺は最初の辺に移る。
方針：次数の等式を消去する。
規約：辺の端点は数値零と一で表す。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、指定辺の join 同型による移送。 -/
lemma initialEdge_eqToIso {m n : ℕ} (h : m = n) :
    (eqToIso (congrArg (fun d : ℕ ↦ (Δ[d] : SSet.{u})) h)).hom.app (Opposite.op ⦋1⦌)
      (stdSimplex.edge m 0 1 (Fin.zero_le _)) = stdSimplex.edge n 0 1 (Fin.zero_le _) := by
  subst n
  simp

/-- 概要：標準単体の join の左の辺は周囲の最初の辺に移る。
方針：左区間の連結写像の値を二つの頂点で計算する。
規約：次数は n+2 に正規化する。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、相対充填で指定する辺の比較。 -/
lemma initialEdgeJoinIso_inl_edge (n : ℕ) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[n] ≫ (initialEdgeJoinIso n).hom) =
      stdSimplex.edge (n + 2) 0 1 (Fin.zero_le _) := by
  have hraw : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[n] ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 n).hom) = stdSimplex.edge (1 + n + 1) 0 1 (Fin.zero_le _) := by
    apply stdSimplex.ext
    intro i
    fin_cases i
    all_goals
      apply Fin.ext
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := 2) (q := n + 1) (r := 2) 2 (by omega)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} 1 2 (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} n 0 PUnit.unit) _).val = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ (by omega)]
      rfl
  rw [initialEdgeJoinIso, Iso.trans_hom, ← Category.assoc, SSet.yonedaEquiv_comp, hraw,
    initialEdge_eqToIso (show 1 + n + 1 = n + 2 by omega)]

/-- 概要：初期ホーンの join 同型は左の辺をホーンの指定された最初の辺に移す。
方針：周囲の標準単体へ含めて左の辺の計算に帰着する。
規約：辺は join の右因子の境界に依存しない。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、cocartesian 性の適用。 -/
lemma initialHornJoinIso_edge (n : ℕ) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) (boundary n : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (horn 1 0) (boundary n) ≫ (initialHornJoinIso n).hom) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n := by
  apply Subtype.ext
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) (boundary n : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (horn 1 0) (boundary n) ≫ (initialHornJoinIso n).hom) ≫
      (horn (n + 2) 0).ι) = _
  rw [Category.assoc, Category.assoc, initialHornJoinIso_hom_ι,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight _ _) _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
  exact initialEdgeJoinIso_inl_edge n

/-- 概要：初期ホーンの join 同型の逆射も周囲の包含と可換。
方針：順方向の可換性を二つの同型の逆射で移す。
規約：右辺は標準単体から join への逆同型を使う。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、coslice の持ち上げ問題の標準化。 -/
lemma initialHornJoinIso_inv_ι (n : ℕ) :
    (initialHornJoinIso.{u} n).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 1 0) (boundary n)).ι =
      (horn (n + 2) 0).ι ≫ (initialEdgeJoinIso n).inv := by
  apply (cancel_epi (initialHornJoinIso n).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
    initialHornJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
