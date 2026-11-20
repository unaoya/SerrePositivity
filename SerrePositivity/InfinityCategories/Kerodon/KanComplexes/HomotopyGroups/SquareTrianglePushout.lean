module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTriangleIntersection
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：正方形は二つの三角形を対角辺で貼り合わせた pushout。
方針：各単体次数で交わりと被覆を検査し、型の pushout を関手圏へ戻す。
規約：通常の単体集合の厳密な pushout。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つの円の交換の符号の幾何的比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SquareTriangles
end SerrePositivity.KST.Spectra.SquareTriangles
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra.SquareTriangles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：各単体次数で二つの三角形の共通部分は対角辺の pullback。
方針：対角辺の包含の単射性と、共通部分の対角辺への因子分解を使う。
規約：単体次数 d は任意。
使われ方：Goerss–Jardine I §7。二つの三角形の pushout の集合での検査。 -/
theorem app_isPullback (d : ℕ) :
    IsPullback ((stdSimplex.δ (1 : Fin 3)).app (Opposite.op ⦋d⦌))
      ((stdSimplex.δ (1 : Fin 3)).app (Opposite.op ⦋d⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u}.app (Opposite.op ⦋d⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u}.app (Opposite.op ⦋d⦌)) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] =>
      f.app (Opposite.op ⦋d⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_diagonal.trans _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_diagonal.symm)
  · intro x y hxy
    apply stdSimplex.ext
    intro r
    have hr := congrArg (fun s => s r) hxy.1
    exact Fin.succAbove_right_injective hr
  · intro s t h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_lower_intersection d s t h

/-- 概要：各単体次数で二つの三角形を対角辺で貼ると正方形になる。
方針：pullback 条件、二つの三角形の被覆、各包含の単射性を使う。
規約：型の圏の pushout。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。単体集合の pushout の次数ごとの検査。 -/
theorem app_isPushout (d : ℕ) :
    IsPushout ((stdSimplex.δ (1 : Fin 3)).app (Opposite.op ⦋d⦌))
      ((stdSimplex.δ (1 : Fin 3)).app (Opposite.op ⦋d⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u}.app (Opposite.op ⦋d⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u}.app (Opposite.op ⦋d⦌)) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u}.app (Opposite.op ⦋d⦌)) :=
    (mono_iff_injective _).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_app_injective d)
  exact Types.isPushout_of_isPullback_of_mono' (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.app_isPullback d) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_lower_cover d)
    (fun s t _ _ h => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_app_injective d h)

/-- 概要：正方形は二つの標準三角形を対角辺で貼り合わせた厳密な pushout。
方針：各単体次数の pushout を評価関手の余極限反映で戻す。
規約：座標の交換は二つの pushout の脚を交換する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの円の交換を二つの三角形の交換へ移す。 -/
theorem isPushout : IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u} where
  w := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_diagonal.trans _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_diagonal.symm
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨d⟩⟩ =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.app_isPushout.{u} d).isColimit)⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
