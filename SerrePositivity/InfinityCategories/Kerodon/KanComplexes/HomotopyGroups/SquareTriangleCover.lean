module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTriangleEmbedding

/-!
概要：正方形の任意の単体は二つの三角形のどちらかに含まれる。
方針：区間の二つの単調な単体を点ごとに比較し、頂点の値の和で三角形へ戻す。
規約：全ての単体次数で代表を構成する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形の二つの三角形の pushout 表示。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SquareTriangles
end SerrePositivity.KST.Spectra.SquareTriangles
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra.SquareTriangles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：二つの区間の頂点の値の和を三角形の頂点とする。
方針：値は 0,1,2 のいずれかになる。
規約：座標の順序には依存しない。
使われ方：Goerss–Jardine I §7。正方形の単体の三角形への因子分解。 -/
def sumIndex (a b : Fin 2) : Fin 3 := ⟨a.val + b.val, by omega⟩

/-- 概要：順序を保つ頂点の組は上側の三角形で元の第一座標へ戻る。
方針：二つの頂点の四つの組を調べる。
規約：第一座標は σ₀。
使われ方：Goerss–Jardine I §7。三角形の代表の第一座標の検査。 -/
theorem sigma_zero_sumIndex {a b : Fin 2} (h : a ≤ b) :
    (SimplexCategory.σ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex a b) = a := by
  fin_cases a <;> fin_cases b <;> norm_num [Fin.le_def] at h
  all_goals rfl

/-- 概要：順序を保つ頂点の組は上側の三角形で元の第二座標へ戻る。
方針：二つの頂点の四つの組を調べる。
規約：第二座標は σ₁。
使われ方：Goerss–Jardine I §7。三角形の代表の第二座標の検査。 -/
theorem sigma_one_sumIndex {a b : Fin 2} (h : a ≤ b) :
    (SimplexCategory.σ (1 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex a b) = b := by
  fin_cases a <;> fin_cases b <;> norm_num [Fin.le_def] at h
  all_goals rfl

/-- 概要：二つの区間の単体の頂点の和から三角形の単体を作る。
方針：和の単調性を使って単体圏の射へ戻す。
規約：d は任意の単体次数。
使われ方：Goerss–Jardine I §7。正方形の単体の実際の三角形の代表。 -/
def sumSimplex {d : ℕ} (s t : (Δ[1] : SSet.{u}) _⦋d⦌) : (Δ[2] : SSet.{u}) _⦋d⦌ :=
  stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk {
    toFun r := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex (s r) (t r)
    monotone' r q hrq := by
      have hs := (stdSimplex.asOrderHom s).monotone hrq
      have ht := (stdSimplex.asOrderHom t).monotone hrq
      exact Nat.add_le_add hs ht })

/-- 概要：点ごとに順序を保つ正方形の単体は上側の三角形から得られる。
方針：二つの射影を各頂点で計算する。
規約：代表は頂点の値の和で与える。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つの三角形の被覆。 -/
theorem upper_sumSimplex {d : ℕ} (s t : (Δ[1] : SSet.{u}) _⦋d⦌)
    (h : ∀ r, s r ≤ t r) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumSimplex s t) = (s, t) := by
  apply Prod.ext
  · apply stdSimplex.ext
    intro r
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sigma_zero_sumIndex (h r)
  · apply stdSimplex.ext
    intro r
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sigma_one_sumIndex (h r)

/-- 概要：逆順に並ぶ正方形の単体は下側の三角形から得られる。
方針：座標を逆順にした上側の式を使う。
規約：代表の値は二つの頂点の和。
使われ方：Goerss–Jardine I §7。下側の三角形による被覆。 -/
theorem lower_sumSimplex {d : ℕ} (s t : (Δ[1] : SSet.{u}) _⦋d⦌)
    (h : ∀ r, t r ≤ s r) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumSimplex s t) = (s, t) := by
  apply Prod.ext
  · apply stdSimplex.ext
    intro r
    change (SimplexCategory.σ (1 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex (s r) (t r)) = s r
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex (s r) (t r) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex (t r) (s r) from Fin.ext (Nat.add_comm _ _)]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sigma_one_sumIndex (h r)
  · apply stdSimplex.ext
    intro r
    change (SimplexCategory.σ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex (s r) (t r)) = t r
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex (s r) (t r) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumIndex (t r) (s r) from Fin.ext (Nat.add_comm _ _)]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sigma_zero_sumIndex (h r)

/-- 概要：二つの区間の単体は点ごとの順序で必ず比較できる。
方針：交差する二つの頂点の値は、どちらの頂点の順序でも単調性に反する。
規約：値域の頂点は 0 と 1 の二つのみ。
使われ方：Goerss–Jardine I §7。正方形の各単体を一つの三角形へ因子分解する。 -/
theorem interval_simplices_comparable {d : ℕ} (s t : (Δ[1] : SSet.{u}) _⦋d⦌) :
    (∀ r, s r ≤ t r) ∨ ∀ r, t r ≤ s r := by
  by_cases h : ∀ r, s r ≤ t r
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨r, hr⟩ := h
    intro q
    by_contra hq
    rcases le_total q r with hqr | hrq
    · have ht := (stdSimplex.asOrderHom t).monotone hqr
      change t q ≤ t r at ht
      omega
    · have hs := (stdSimplex.asOrderHom s).monotone hrq
      change s r ≤ s q at hs
      omega

/-- 概要：正方形の全単体は二つの三角形の像に含まれる。
方針：点ごとの順序で場合分けし、和の単体を代表に取る。
規約：射影を含む全ての退化単体も扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つの三角形の pushout の全射性。 -/
theorem upper_lower_cover (d : ℕ) :
    Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u}.app (Opposite.op ⦋d⦌)) ∪
      Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u}.app (Opposite.op ⦋d⦌)) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.interval_simplices_comparable p.1 p.2 with h | h
  · exact Or.inl ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumSimplex p.1 p.2, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_sumSimplex _ _ h⟩
  · exact Or.inr ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sumSimplex p.1 p.2, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_sumSimplex _ _ h⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
