module


public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
分割で生成：docstring を書き直すこと
概要：標準単体の最後の頂点への区間収縮。
方針：区間の零値では元の値を、一区間側では最後の頂点を取る単調写像を使う。
規約：最後のホーンも保つ。Kan 性やモデル構造を仮定しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。境界のホモトピー類による充填判定。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SimplexLastContraction
end SerrePositivity.KST.Spectra.SimplexLastContraction
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction
open _root_.SerrePositivity.KST.Spectra.SimplexLastContraction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準単体の単体を区間の切り替え位置以後で最後の頂点にする。
方針：元の二つの単調写像から単調写像を作る。
規約：区間の値が零でない場合は最後の頂点。
使われ方：Goerss–Jardine I §7。収縮の各次数の定義。 -/
def simplex {n d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) : (Δ[n] : SSet.{u}) _⦋d⦌ :=
  stdSimplex.objMk {
    toFun i := if t i = 0 then s i else Fin.last n
    monotone' := by
      intro i j hij
      dsimp only
      by_cases hi : t i = 0
      · by_cases hj : t j = 0
        · simp only [ite_eq_left hi, ite_eq_left hj]
          exact stdSimplex.monotone_apply s hij
        · simp only [ite_eq_left hi, ite_eq_right hj]
          exact Fin.le_last _
      · by_cases hj : t j = 0
        · have h := stdSimplex.monotone_apply t hij
          have hti : t i = 0 := by
            change t i ≤ t j at h
            rw [hj] at h
            exact le_antisymm h (Fin.zero_le _)
          exact (hi hti).elim
        · simp only [ite_eq_right hi, ite_eq_right hj]
          exact le_rfl }

/-- 概要：収縮した単体の頂点値の計算。
方針：標準単体の objMk の評価式を使う。
規約：任意の単体次数。
使われ方：Goerss–Jardine I §7。自然性とホーン保存の計算。 -/
@[simp]
theorem simplex_apply {n d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex s t i = if t i = 0 then s i else Fin.last n := rfl

/-- 概要：区間の切り替えによる標準単体の単体的な収縮写像。
方針：各単体次数で simplex を用い、前合成に関する定義上の自然性を使う。
規約：始点で恒等射、終点で最後の頂点の定数射。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。境界を正規化するホモトピー。 -/
def map (n : ℕ) : (Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) where
  app m := ↾(fun p : ((Δ[n] : SSet.{u}).obj m × (Δ[1] : SSet.{u}).obj m) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex p.1 p.2)
  naturality m m' f := by
    ext p
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：収縮の始点は標準単体の恒等射。
方針：区間の始点の値が常に零であることを使う。
規約：通常の単体集合の射の等式。
使われ方：Goerss–Jardine I §7。ホモトピーの始点条件。 -/
@[reassoc (attr := simp)]
theorem zero (n : ℕ) : SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.map.{u} n = 𝟙 (Δ[n] : SSet.{u}) := by
  apply NatTrans.ext
  funext ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex s (SSet.ι₀.app _ s).2 i = s i
  rfl

/-- 概要：標準単体の最後の頂点。
方針：零単体と Fin の標準同値を使う。
規約：零次元でも定義する。
使われ方：Goerss–Jardine I §7。収縮の終点。 -/
def vertex (n : ℕ) : (Δ[n] : SSet.{u}) _⦋0⦌ :=
  stdSimplex.obj₀Equiv.symm (Fin.last n)

/-- 概要：収縮の終点は最後の頂点の定数射。
方針：区間の終点の値が常に一であることを使う。
規約：通常の単体集合の射の等式。
使われ方：Goerss–Jardine I §7。ホモトピーの終点条件。 -/
@[reassoc (attr := simp)]
theorem one (n : ℕ) : SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.map.{u} n = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.vertex n) := by
  apply NatTrans.ext
  funext ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex s (SSet.ι₁.app _ s).2 i = Fin.last n
  rfl

/-- 概要：最後の頂点への収縮は最後のホーンを保つ。
方針：ホーンの単体が欠く最後以外の頂点は、切り替え後も欠けたままである。
規約：任意の単体次数と任意の区間単体。
使われ方：Goerss–Jardine I §7。境界上の射の正規化。 -/
theorem simplex_mem_horn {n d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌)
    (hs : s ∈ (horn n (Fin.last n)).obj _) (t : (Δ[1] : SSet.{u}) _⦋d⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex s t ∈ (horn n (Fin.last n)).obj _ := by
  rw [mem_horn_iff_notMem_range] at hs ⊢
  obtain ⟨j, hj, hjs⟩ := hs
  refine ⟨j, hj, ?_⟩
  rintro ⟨i, hi⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.simplex_apply] at hi
  by_cases ht : t i = 0
  · rw [ite_eq_left ht] at hi
    exact hjs ⟨i, hi⟩
  · rw [ite_eq_right ht] at hi
    exact hj hi.symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
