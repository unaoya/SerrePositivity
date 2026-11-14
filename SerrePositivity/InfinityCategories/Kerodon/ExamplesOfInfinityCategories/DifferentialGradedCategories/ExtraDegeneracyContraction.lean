module

public meta import SerrePositivity.Util.Citation
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedSpace
public import Mathlib.Tactic.Abel

/-!
# extra degeneracy による正次数サイクルの充填

概要：先頭頂点を付加する写像が正次数で鎖収縮の等式を満たす。
方針：最初の面を分離し、残る交代和を一つ低い微分と相殺する。
規約：KST Construction A.5 の普遍単体模型に適用する。
使われ方：AW/shuffle の比較ホモトピーの各次数で普遍サイクルを埋める。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory AlgebraicTopology
open scoped Simplicial

/-- 概要：extra degeneracy は正次数で微分との鎖収縮等式を満たす。
方針：第零面を恒等へ同定し、残る面を一つ低い次数へ移す。
規約：KST A.5、任意の前加法圏の増大単体的対象で成立。
使われ方：普遍な比較の差を再帰的に充填する。 -/
lemma extraDegeneracy_positive_boundary {C : Type u} [Category.{v} C] [Preadditive C]
    {X : SimplicialObject.Augmented C} (ed : SimplicialObject.Augmented.ExtraDegeneracy X)
    (n : ℕ) :
    ed.s (n + 1) ≫ AlternatingFaceMapComplex.objD X.left (n + 1) +
      AlternatingFaceMapComplex.objD X.left n ≫ ed.s n = 𝟙 _ := by
  simp only [AlternatingFaceMapComplex.objD, Preadditive.comp_sum, Preadditive.comp_zsmul,
    Preadditive.sum_comp, Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, ed.s_comp_δ₀, Fin.val_succ,
    ed.s_comp_δ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
  abel

/-- 概要：正次数サイクルは extra degeneracy による一段上の鎖の境界。
方針：収縮等式をサイクルに評価し、低い微分の項を零にする。
規約：KST A.5、整数加群の非被約な交代面複体。
使われ方：普遍模型の比較サイクルの明示的な充填。 -/
lemma extraDegeneracy_fill_cycle {X : SimplicialObject.Augmented (ModuleCat.{u} ℤ)}
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X) (n : ℕ)
    (x : X.left.obj (Opposite.op ⦋n + 1⦌))
    (hx : AlternatingFaceMapComplex.objD X.left n x = 0) :
    AlternatingFaceMapComplex.objD X.left (n + 1) (ed.s (n + 1) x) = x := by
  have he := congrArg (fun f ↦ f x) (extraDegeneracy_positive_boundary ed n)
  change AlternatingFaceMapComplex.objD X.left (n + 1) (ed.s (n + 1) x) +
    ed.s n (AlternatingFaceMapComplex.objD X.left n x) = x at he
  simpa only [hx, map_zero, add_zero] using he

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.7.2.12" (partial := component) "仮定：アーベル圏の単体的対象と、増大を持つ場合は指定した追加退化（Lean が強い：アーベル圏と指定した追加退化の場合）。結論：単体的対象と非負鎖複体の Dold–Kan 同値を与え、追加退化から増大への切断との合成を恒等に結ぶ単体的ホモトピー、および交代面微分の縮約式を与える（この仮定での HA の結論の一部に一致）。任意の鎖縮約から Δ−∞ への拡張を回復する逆向きは含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.extraDegeneracy_positive_boundary
