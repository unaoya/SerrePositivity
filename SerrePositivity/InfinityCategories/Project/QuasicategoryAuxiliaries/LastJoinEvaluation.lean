module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-! # 標準単体の最後の頂点への join の評価

概要：標準単体の右に点を加えた join を、その点を最後の頂点へ送って元の単体へ写す。
方針：標準単体どうしの join の同型を通じ、最後の二頂点を重ねる単調写像を使う。
規約：左の因子では恒等射、右の因子は最後の頂点へ送る。
使われ方：S4 の五頂点図式から長方形への余錐の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：最後の二頂点を重ねる単調写像。
方針：頂点番号と n の最小値を取る。
規約：始域は n+2 頂点、終域は n+1 頂点。
使われ方：点を最後の頂点へ送る join の評価。 -/
def stableLastCollapseOrderHom (n : ℕ) : Fin (n + 2) →o Fin (n + 1) where
  toFun i := ⟨min i.val n, by omega⟩
  monotone' _ _ h := min_le_min_right n h

/-- 概要：標準単体の右に加えた点を最後の頂点へ送る射。
方針：標準 join 同型の後で最後の二頂点を重ねる。
規約：元の単体の頂点番号を保つ。
使われ方：長方形の二つの座標の余錐。 -/
def stableLastJoinEvaluation (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0] ⟶ Δ[n] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    stdSimplex.map (SimplexCategory.mkHom (stableLastCollapseOrderHom n))

/-- 概要：join の評価の各頂点の番号は連結した番号を最後の頂点で切り詰めたもの。
方針：標準 join 同型と後合成の定義を計算する。
規約：退化単体も含む。
使われ方：切断の左右における評価の計算。 -/
lemma stableLastJoinEvaluation_app_val (n d : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[n] : SSet.{u}) Δ[0] d) (i : Fin (d + 1)) :
    ((stableLastJoinEvaluation n).app (Opposite.op ⦋d⦌) s i).val =
      min (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode n 0 d s i).val n := rfl

/-- 概要：切断より前の頂点では join の評価は左因子の値を保つ。
方針：連結写像の左側の式と頂点番号の上界を使う。
規約：左因子の補った次数は空でもよい。
使われ方：五頂点図式の単体の回収。 -/
lemma stableLastJoinEvaluation_app_of_lt (n d : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[n] : SSet.{u}) Δ[0] d) (i : Fin (d + 1)) (hi : i.val < s.1.val) :
    (stableLastJoinEvaluation n).app (Opposite.op ⦋d⦌) s i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n s.1.val s.2.1 ⟨i.val, hi⟩ := by
  apply Fin.ext
  rw [stableLastJoinEvaluation_app_val]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ hi]
  exact Nat.min_eq_left (Nat.le_of_lt_succ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ s.2.1) ⟨i.val, hi⟩).isLt)

/-- 概要：切断以降の頂点は元の標準単体の最後の頂点へ送られる。
方針：連結写像の右側の式を最後の頂点番号で切り詰める。
規約：右因子は標準零単体。
使われ方：長方形の終端角の回収。 -/
lemma stableLastJoinEvaluation_app_of_ge (n d : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[n] : SSet.{u}) Δ[0] d) (i : Fin (d + 1)) (hi : s.1.val ≤ i.val) :
    (stableLastJoinEvaluation n).app (Opposite.op ⦋d⦌) s i = Fin.last n := by
  apply Fin.ext
  rw [stableLastJoinEvaluation_app_val]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ hi]
  change min (n + 1 + _) n = n
  omega

/-- 概要：右に点を付けた評価は左因子上で恒等射。
方針：全ての頂点が切断より前にあることを使う。
規約：単体的な射の等式。
使われ方：長方形の余錐の基底の固定。 -/
lemma stableLastJoinEvaluation_inl (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ stableLastJoinEvaluation n = 𝟙 Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  exact stableLastJoinEvaluation_app_of_lt n d (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl s) i i.isLt

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
