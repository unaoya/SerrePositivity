module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Alexander–Whitney 対角の単体の切断

概要：Berger–Fresse §1.1.4 の AW 公式に現れる連続した頂点区間への制限を定義する。
方針：区間の包含を単体圏の射として構成し、関手性から自然性と反復制限を証明する。
規約：区間 [a,a+b] は b 単体であり、隣り合う区間は端点を一つ共有する。
使われ方：正規化鎖の AW 対角の自然性と余結合性を生成元で検証する。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- 概要：連続する b+1 個の頂点を選ぶ包含（Berger–Fresse §1.1.4）。
方針：頂点番号 k を a+k に送る単調写像を使う。
規約：a+b ≤ n を仮定して [b] から [n] へ送る。
使われ方：AW の前半と後半の面を同じ定義で扱う。 -/
def segmentMap (a b n : ℕ) (h : a + b ≤ n) : ⦋b⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨a + k.val, by omega⟩
      monotone' := fun _ _ hk => Nat.add_le_add_left hk a }

/-- 概要：全頂点を選ぶ区間包含は恒等射（Berger–Fresse §1.1.4）。
方針：各頂点の番号を比較する。
規約：始点は 0、長さは n。
使われ方：AW の次数零の因子に関する余単位を計算する。 -/
@[simp] lemma segmentMap_zero (n : ℕ) : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 n n (by omega) = 𝟙 _ := by
  ext k : 3
  simp [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap]

/-- 概要：頂点区間の包含を二度行うと始点が加算される（Berger–Fresse §1.1.4）。
方針：各頂点で自然数の加法の結合則を使う。
規約：内側の区間 [c,c+d] は [b] の中にある。
使われ方：AW の反復対角の三つの因子を比較する。 -/
lemma segmentMap_comp (a b n c d : ℕ) (h : a + b ≤ n) (k : c + d ≤ b) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap c d b k ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap (a + c) d n (by omega) := by
  ext i : 3
  apply Fin.ext
  change a + (c + i.val) = (a + c) + i.val
  omega

/-- 概要：単体を連続した頂点区間へ制限する（Berger–Fresse §1.1.4）。
方針：単体集合の反変関手を区間包含に適用する。
規約：出力は b 単体である。
使われ方：AW 対角の生成元公式を記述する。 -/
def cut (X : SSet) {n : ℕ} (x : X _⦋n⦌) (a b : ℕ) (h : a + b ≤ n) : X _⦋b⦌ :=
  X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).op x

/-- 概要：単体集合の射は頂点区間への制限と可換する（Berger–Fresse §1.1.4）。
方針：自然変換の自然性を単体で評価する。
規約：任意の単体集合の射について成立する。
使われ方：単体的オペラッド合成に対する AW の自然性を得る。 -/
lemma cut_natural {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌)
    (a b : ℕ) (h : a + b ≤ n) :
    f.app _ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a b h) = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y (f.app _ x) a b h := by
  exact congrArg (fun g => g x) (f.naturality (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).op)

/-- 概要：全頂点への制限は元の単体である（Berger–Fresse §1.1.4）。
方針：区間包含が恒等射であることを使う。
規約：零次単体も含む。
使われ方：AW の左右の余単位の計算に用いる。 -/
@[simp] lemma cut_zero (X : SSet) {n : ℕ} (x : X _⦋n⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 n (by omega) = x := by
  simp [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut]

/-- 概要：単体の反復切断は始点を加算した切断に等しい（Berger–Fresse §1.1.4）。
方針：区間包含の合成と単体集合の関手性を使う。
規約：等式の両辺は同じ d 単体であり、次数の移送は不要である。
使われ方：AW 対角の余結合性を切断ごとに証明する。 -/
lemma cut_cut (X : SSet) {n : ℕ} (x : X _⦋n⦌)
    (a b c d : ℕ) (h : a + b ≤ n) (k : c + d ≤ b) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a b h) c d k = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x (a + c) d (by omega) := by
  change (X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).op ≫ X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap c d b k).op) x = _
  rw [← X.map_comp]
  change X.map ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap c d b k ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).op) x = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap_comp]
  rfl

end SerrePositivity.SimplicialChains.AlexanderWhitney
