module

public import SerrePositivity.KST.Comparison.FatNormalFormAction
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 標準形の次元による fat realization の骨格

概要：全射な標準形の終域の次元が n 以下の元からなる有限骨格を構成する。
方針：単体作用による正規化の次元の減少から部分単体集合の条件を確認する。
規約：Segal 1974 Proposition 1.6、Appendix A の fat realization の濾過。
使われ方：有限骨格の付着の普遍性と無限骨格への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open scoped Simplicial

/--
概要：fat realization の n 次元までの骨格。
方針：正規化した全射の終域の次元の上限で定義する。
規約：n 番目の行を含む inclusive な番号付け。
使われ方：有限骨格の帰納の対象。
-/
def fatSkeleton (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    (fatRealization F).Subcomplex where
  obj d := {y | (fatDegreeNormalize F d y).degree.len ≤ n}
  map θ y hy := (fatNormalDegree_action_le F θ y).trans hy

/--
概要：fat realization の骨格は次元に関して増加する。
方針：標準形の次元の不等式の推移性を使う。
規約：同じ実対象の部分単体集合としての包含。
使われ方：骨格の順序列の構成。
-/
theorem fatSkeleton_monotone (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : Monotone (fatSkeleton F) := by
  intro n m h d y hy
  exact hy.trans h

/--
概要：各次数では、その次数までの骨格が既に全体である。
方針：標準形の終域の次元は単体の次数以下である。
規約：単体集合全体の有限次元性は要求しない。
使われ方：骨格の余極限と fat realization の同定。
-/
theorem fatSkeleton_obj_eq_univ (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (n : ℕ) (h : d.unop.len ≤ n) :
    (fatSkeleton F n).obj d = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact (fatNormalDegree_le F d y).trans h

/--
概要：全ての有限骨格の和は fat realization 全体である。
方針：任意の単体をその次数の骨格へ入れる。
規約：部分単体集合の束における等式。
使われ方：無限骨格への移行の対象の同定。
-/
theorem iSup_fatSkeleton_eq_top (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (⨆ n, fatSkeleton F n) = ⊤ := by
  ext d y
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.top_obj, Set.mem_univ,
    iff_true]
  exact ⟨d.unop.len, fatNormalDegree_le F d y⟩

/--
概要：n 行と標準 n 単体の積の像は n 骨格に含まれる。
方針：包含で正規化し、像の包含の単射から次元の不等式を得る。
規約：標準単体の元に全射性は要求しない。
使われ方：各行の構造写像の骨格への因子化。
-/
theorem fatRealizationInclusion_mem_skeleton (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (n : ℕ) (d : SimplexCategoryᵒᵖ) (x : (F.obj (op ⦋n⦌)).obj d) (t : Δ[n].obj d) :
    (fatRealizationInclusion F n).app d (x, t) ∈ (fatSkeleton F n).obj d := by
  change (fatDegreeNormalize F d ((fatRealizationInclusion F n).app d (x, t))).degree.len ≤ n
  rw [fatDegreeNormalize_inclusion]
  exact SimplexCategory.len_le_of_mono (image.ι (SSet.stdSimplex.objEquiv t))

end SerrePositivity.KST.Comparison
