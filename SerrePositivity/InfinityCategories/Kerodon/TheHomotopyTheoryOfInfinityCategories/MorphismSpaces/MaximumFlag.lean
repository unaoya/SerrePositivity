module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomNaturality

/-!
概要：最大元座標の切断となる path の旗。
方針：最初の頂点から各頂点までの区間に最後の頂点を加え、増大する path の列を作る。
規約：切断は各次数の比較に用い、pinched 模型からの自然な逆射とは主張しない。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Theorem 4.6.7.5（Tag 01LE）、比較の単射性と相対比較の準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：指定頂点までの区間に最後の頂点を加えた path。
方針：各頂点の番号が j 以下か、最後の頂点であるという集合を取る。
規約：始点は最初の頂点、終点は追加した最後の頂点。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、最大元座標の切断。 -/
def maximumFlagPath {n : ℕ} (j : Fin (n + 1)) :
    Path (ULift.up (0 : Fin (n + 1)).castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := {k | k.down.val ≤ j.val ∨ k.down = Fin.last (n + 1)}
  left := Or.inl (Nat.zero_le _)
  right := Or.inr rfl
  left_le k _ := Fin.zero_le k.down
  le_right k _ := Fin.le_last k.down

/-- 概要：旗の各 path の最大の前終点は指定した頂点。
方針：指定した頂点の所属と、それより大きい前終点がないことを使う。
規約：最後の頂点を除く最大元を取る。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の入力単体の回収。 -/
lemma pathLastMaximum_maximumFlagPath {n : ℕ} (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (maximumFlagPath.{u} j) = j := by
  apply le_antisymm
  · have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem (maximumFlagPath.{u} j)
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (maximumFlagPath.{u} j)).val ≤ j.val ∨
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (maximumFlagPath.{u} j)).castSucc = Fin.last (n + 1) at h
    rcases h with h | h
    · exact h
    · have hv := congrArg Fin.val h
      have hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (maximumFlagPath.{u} j)).val < n + 1 :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (maximumFlagPath.{u} j)).isLt
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (maximumFlagPath.{u} j)).val = n + 1 at hv
      omega
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum
    exact Or.inl le_rfl

/-- 概要：指定頂点までの path の旗は順序圏からの関手。
方針：頂点の増加に対し区間の包含を使う。
規約：値域は最初の頂点から最後の頂点への path の包含順序。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、標準単体を Hom 立方体に含める旗。 -/
def maximumFlagFunctor (n : ℕ) :
    ULift.{u} (Fin (n + 1)) ⥤
      Path (ULift.up (0 : Fin (n + 1)).castSucc : ULift.{u} (Fin (n + 2)))
        (ULift.up (Fin.last (n + 1))) where
  obj j := maximumFlagPath j.down
  map {i j} f := ⟨⟨⟨by
    intro k hk
    rcases hk with hk | hk
    · exact Or.inl (hk.trans f.le)
    · exact Or.inr hk⟩⟩⟩

/-- 概要：標準単体から最初と最後の頂点の間の Hom の nerve への旗の射。
方針：標準単体の nerve 表示と旗の関手の nerve を合成する。
規約：次数 n ごとに定義する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の各次数での切断。 -/
def maximumFlagMap (n : ℕ) : (Δ[n] : SSet.{u}) ⟶
    nerve (Path (ULift.up (0 : Fin (n + 1)).castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :=
  (stdSimplex.isoNerve n).hom ≫ nerveMap (maximumFlagFunctor n)

/-- 概要：旗を最大元で評価すると標準単体の恒等になる。
方針：標準単体の各頂点で旗の最大元を計算する。
規約：Hom の始点は 0、終点は追加した最後の頂点。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較の単射性の回収写像。 -/
lemma maximumFlagMap_comp_pathLastMaximumMap (n : ℕ) :
    maximumFlagMap.{u} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin (n + 1)) = 𝟙 Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro k
  let P := (nerveMap (maximumFlagFunctor.{u} n)).app (Opposite.op ⦋d⦌)
    ((stdSimplex.isoNerve n).hom.app (Opposite.op ⦋d⦌) s)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin (n + 1))).app (Opposite.op ⦋d⦌) P) k = s k
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (P.obj k) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply 0 P k
    _ = s k := pathLastMaximum_maximumFlagPath (s k)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
