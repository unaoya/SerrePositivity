module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction

/-!
概要：最後のホーンの最後の頂点への収縮。
方針：標準単体の明示的な収縮をホーンへ制限し、包含で二つの端点を検出する。
規約：ホーンの次元は n+1。零次元の空なホーンは含まない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。境界の正規化。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.LastHornContraction
end SerrePositivity.KST.Spectra.LastHornContraction
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction
open _root_.SerrePositivity.KST.Spectra.LastHornContraction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：最後のホーンの最後の頂点。
方針：標準単体の最後の頂点は零番目の頂点を欠くことを使う。
規約：次元 n+1 は正。
使われ方：Goerss–Jardine I §7。収縮の定数値。 -/
def vertex (n : ℕ) : (horn.{u} (n + 1) (Fin.last (n + 1))) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.vertex (n + 1), by
    rw [mem_horn_iff_notMem_range]
    refine ⟨0, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · rintro ⟨i, hi⟩
      change Fin.last (n + 1) = 0 at hi
      have := congrArg Fin.val hi
      simp at this⟩

/-- 概要：最後のホーン上に制限した収縮写像。
方針：各次数の収縮後の単体がホーンを保つことを使う。
規約：標準単体への包含と厳密に可換。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。境界のホーン上での収縮。 -/
def map (n : ℕ) :
    (horn.{u} (n + 1) (Fin.last (n + 1)) : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
      (horn.{u} (n + 1) (Fin.last (n + 1)) : SSet.{u}) where
  app m := ↾(fun p : ((horn.{u} (n + 1) (Fin.last (n + 1))).obj m × (Δ[1] : SSet.{u}).obj m) ↦
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex p.1.val p.2,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex_mem_horn p.1.val p.1.property p.2⟩)
  naturality m m' f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：ホーンの収縮を含めると標準単体の収縮に一致。
方針：制限写像の定義を比較する。
規約：区間との積では包含を第一成分へ作用させる。
使われ方：Goerss–Jardine I §7。端点と基点の比較。 -/
@[reassoc]
theorem map_ι (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map.{u} n ≫ (horn (n + 1) (Fin.last (n + 1))).ι =
    (horn (n + 1) (Fin.last (n + 1))).ι ▷ (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.map (n + 1) := rfl

/-- 概要：ホーンの収縮の始点は恒等射。
方針：包含の単射性と標準単体の端点の計算で示す。
規約：ホーン上の射の厳密な等式。
使われ方：Goerss–Jardine I §7。境界の正規化の初期値。 -/
@[reassoc (attr := simp)]
theorem zero (n : ℕ) : SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map.{u} n = 𝟙 _ := by
  apply (cancel_mono (horn (n + 1) (Fin.last (n + 1))).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map_ι, ← Category.assoc, SSet.ι₀_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.zero, Category.comp_id, Category.id_comp]

/-- 概要：ホーンの収縮の終点は最後の頂点に定数。
方針：包含へ合成して標準単体の終点の計算へ移す。
規約：非空なホーンの定数射。
使われ方：Goerss–Jardine I §7。正規化後のホーンの境界条件。 -/
@[reassoc (attr := simp)]
theorem one (n : ℕ) : SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map.{u} n = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.vertex n) := by
  apply (cancel_mono (horn (n + 1) (Fin.last (n + 1))).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map_ι, ← Category.assoc, SSet.ι₁_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.one, SSet.comp_const, SSet.const_comp]
  rfl

/-- 概要：最後のホーンの恒等射から最後の頂点の定数射へのホモトピー。
方針：制限した収縮写像と端点の式を束ねる。
規約：実際の区間ホモトピー。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。境界の充填判定の幾何的入力。 -/
def homotopy (n : ℕ) : SSet.Homotopy
    (𝟙 (horn.{u} (n + 1) (Fin.last (n + 1)) : SSet.{u})) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.vertex n)) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map n
  h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.zero n
  h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.one n
  rel := by ext m ⟨⟨x, hx⟩, t⟩; exact hx.elim

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.homotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.homotopy := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.homotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.map_ι := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.map_ι_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map_ι_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.one := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.one_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.one_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.vertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.vertex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.zero := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.zero_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.zero_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.homotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.homotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.map._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.map._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.map._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.LastHornContraction.vertex._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.vertex._proof_1
