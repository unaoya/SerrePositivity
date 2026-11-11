module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Index
public import Mathlib.Tactic.CrossRefAttribute

/-! # 任意の単体的集合の右 pinched 写像空間

概要：先頭の面を始点に潰し、最終頂点を終点に固定した単体から写像空間を作る。
方針：添字写像を最終点を固定して延長し、両条件が引き戻しで保たれることを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：dg nerve の線形写像空間の比較先。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom

open CategoryTheory Opposite
open scoped _root_.Simplicial

variable {X : SSet.{u}} (x y : X _⦋0⦌)

/-- 概要：頂点を全て同じ零単体にする定値単体。
方針：零単体への唯一の射で引き戻す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面全体の固定条件。 -/
def constant (x : X _⦋0⦌) (n : ℕ) : X _⦋n⦌ :=
  X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x

/-- 概要：定値単体の引き戻しは定値単体。
方針：零単体への射の一意性と反変関手の合成則を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面条件の保存。 -/
lemma constant_pullback {m n : SimplexCategory} (α : m ⟶ n) :
    X.map α.op (constant x n.len) = constant x m.len := by
  simp only [constant, ← Functor.map_comp_apply, ← op_comp]
  rfl

/-- 概要：右 pinched Hom の n 単体は、先頭面が x に定値で最終頂点が y の (n+1) 単体。
方針：通常の単体に二つの等式を添える。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched Hom の各次数。 -/
structure Simplex (n : ℕ) where
  /-- 元の単体的集合の (n+1) 単体。 -/
  val : X _⦋n + 1⦌
  /-- 先頭の n+1 頂点が張る面全体は始点に定値。 -/
  source : X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op val = constant x n
  /-- 最終頂点は終点。 -/
  target : X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op val = y

namespace Simplex

variable {x y}

/-- 概要：右 pinched 単体は元の単体で一意に決まる。
方針：条件は命題なので証明の一意性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単体的恒等則と合成則。 -/
lemma ext {n : ℕ} {s t : Simplex x y n} (h : s.val = t.val) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- 概要：添字写像の最終点固定延長で右 pinched 単体を引き戻す。
方針：先頭面および最終頂点と延長写像の可換性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched Hom の面と退化。 -/
def pullback {m n : SimplexCategory} (s : Simplex x y n.len) (α : m ⟶ n) :
    Simplex x y m.len where
  val := X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).op s.val
  source := by
    calc
      X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front m.len).op (X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).op s.val) =
          X.map α.op (X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n.len).op s.val) := by
        simpa only [op_comp, Functor.map_comp_apply] using
          congrArg (fun θ => X.map θ.op s.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_extend α)
      _ = constant x m.len := by rw [s.source, constant_pullback]
  target := by
    calc
      X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex m.len).op (X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).op s.val) =
          X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n.len).op s.val := by
        simpa only [op_comp, Functor.map_comp_apply] using
          congrArg (fun θ => X.map θ.op s.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex_extend α)
      _ = y := s.target

/-- 概要：右 pinched 単体の引き戻しは恒等射を保つ。
方針：延長の恒等則と X の恒等則を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単体的恒等則。 -/
lemma pullback_id {n : SimplexCategory} (s : Simplex x y n.len) :
    s.pullback (𝟙 n) = s := by
  apply ext
  change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (𝟙 n)).op s.val = s.val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend_id]
  exact Functor.map_id_apply X _ s.val

/-- 概要：右 pinched 単体の引き戻しは反変に合成する。
方針：延長の合成則と X の反変関手の合成則を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単体的合成則。 -/
lemma pullback_comp {l m n : SimplexCategory} (s : Simplex x y n.len)
    (α : l ⟶ m) (β : m ⟶ n) : (s.pullback β).pullback α = s.pullback (α ≫ β) := by
  apply ext
  simp only [pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend_comp, op_comp, Functor.map_comp_apply]

end Simplex

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：任意の単体的集合と二頂点に対する右 pinched 写像空間。
方針：先頭面と最終頂点を固定した単体を、最終点固定延長で引き戻す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：dg nerve の Kan 写像空間の基礎。 -/
@[kerodon 01KX]
def pinchedHom {X : SSet.{u}} (x y : X _⦋0⦌) : SSet.{u} where
  obj n := PinchedHom.Simplex x y n.unop.len
  map f := ↾fun s => s.pullback f.unop
  map_id _ := by
    ext s
    exact s.pullback_id
  map_comp f g := by
    ext s
    exact (s.pullback_comp g.unop f.unop).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
