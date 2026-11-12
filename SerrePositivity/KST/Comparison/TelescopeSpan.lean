module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplicialSumPullbacks
public import SerrePositivity.KST.Comparison.SpanCylinderFunctor
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# 偶数・奇数段による telescope の span

概要：順序列の辺を偶数段と奇数段の頂点へ結び、telescope の二重写像円筒の span を作る。
方針：辺を偶数から始まる辺と奇数から始まる辺の和で添字付けする。
規約：Segal 1974 Lemma 1.8、p.298 の二重写像円筒の模型。
使われ方：順序列の各自然性の四角形を、Lemma 1.7 の二面へまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：telescope の辺の始まる段階。
方針：左の和では偶数段、右の和では奇数段を取る。
規約：各自然数から次の段階への辺をちょうど一つずつ表す。
使われ方：辺の余積の対象。
-/
def telescopeEdgeDegree : ℕ ⊕ ℕ → ℕ
  | .inl n => 2 * n
  | .inr n => 2 * n + 1

/--
概要：各辺の偶数側の頂点の添字。
方針：奇数から始まる辺は次の偶数頂点へ入れる。
規約：値 n は段階 2n を表す。
使われ方：telescope の span の左脚。
-/
def telescopeEvenIndex : ℕ ⊕ ℕ → ℕ
  | .inl n => n
  | .inr n => n + 1

/--
概要：各辺の奇数側の頂点の添字。
方針：二種類の辺を同じ奇数頂点へ入れる。
規約：値 n は段階 2n+1 を表す。
使われ方：telescope の span の右脚。
-/
def telescopeOddIndex : ℕ ⊕ ℕ → ℕ
  | .inl n => n
  | .inr n => n

/--
概要：辺の始点から偶数側の頂点へ順序の射が存在する。
方針：二種類の辺を場合分けする。
規約：恒等射または一段階の遷移。
使われ方：順序列の関手を左脚に適用する。
-/
theorem telescopeEdgeDegree_le_even (i : ℕ ⊕ ℕ) :
    telescopeEdgeDegree i ≤ 2 * telescopeEvenIndex i := by
  cases i <;> simp only [telescopeEdgeDegree, telescopeEvenIndex] <;> omega

/--
概要：辺の始点から奇数側の頂点へ順序の射が存在する。
方針：二種類の辺を場合分けする。
規約：一段階の遷移または恒等射。
使われ方：順序列の関手を右脚に適用する。
-/
theorem telescopeEdgeDegree_le_odd (i : ℕ ⊕ ℕ) :
    telescopeEdgeDegree i ≤ 2 * telescopeOddIndex i + 1 := by
  cases i <;> simp only [telescopeEdgeDegree, telescopeOddIndex] <;> omega

/--
概要：順序列から作る telescope の span。
方針：各段階の余積の間に、関手の恒等射と遷移射をまとめる。
規約：中央は辺、左は偶数段、右は奇数段の余積。
使われ方：二重写像円筒を取って telescope を得る。
-/
def telescopeSpan (F : ℕ ⥤ SSet.{u}) : WalkingSpan ⥤ SSet.{u} :=
  span
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex (B := fun n => F.obj (2 * n)) telescopeEvenIndex
      (fun i => F.map (homOfLE (telescopeEdgeDegree_le_even i))))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex (B := fun n => F.obj (2 * n + 1)) telescopeOddIndex
      (fun i => F.map (homOfLE (telescopeEdgeDegree_le_odd i))))

/--
概要：順序列の自然変換が誘導する telescope の span の射。
方針：辺・偶数・奇数の各余積で、対応する段階の成分を取る。
規約：二つの可換性は元の自然変換の遷移射への自然性。
使われ方：telescope の比較写像。
-/
def telescopeSpanMap {F G : ℕ ⥤ SSet.{u}} (α : F ⟶ G) : telescopeSpan F ⟶ telescopeSpan G :=
  spanHomMk
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap (fun i => α.app (telescopeEdgeDegree i)))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap (fun n => α.app (2 * n)))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap (fun n => α.app (2 * n + 1)))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_commSq
      (B := fun n => F.obj (2 * n)) (D := fun n => G.obj (2 * n)) telescopeEvenIndex
      (fun i => F.map (homOfLE (telescopeEdgeDegree_le_even i)))
      (fun i => α.app (telescopeEdgeDegree i))
      (fun n => α.app (2 * n))
      (fun i => G.map (homOfLE (telescopeEdgeDegree_le_even i)))
      (fun _ => ⟨α.naturality _⟩)).w
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_commSq
      (B := fun n => F.obj (2 * n + 1)) (D := fun n => G.obj (2 * n + 1)) telescopeOddIndex
      (fun i => F.map (homOfLE (telescopeEdgeDegree_le_odd i)))
      (fun i => α.app (telescopeEdgeDegree i))
      (fun n => α.app (2 * n + 1))
      (fun i => G.map (homOfLE (telescopeEdgeDegree_le_odd i)))
      (fun _ => ⟨α.naturality _⟩)).w

end SerrePositivity.KST.Comparison
