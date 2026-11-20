module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTrianglePushout

/-!
概要：正方形の二つの三角形の外側の四つの辺。
方針：面と退化写像の恒等式により各射影を計算する。
規約：共通の対角辺以外の面を扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形の境界を基点へ潰す条件の比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SquareTriangles
end SerrePositivity.KST.Spectra.SquareTriangles
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra.SquareTriangles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：上側の三角形の零番目の面は正方形の上辺。
方針：第一射影は恒等射、第二射影は終点に定数となる。
規約：頂点の組は (t,1)。
使われ方：Goerss–Jardine I §7。正方形の境界固定条件。 -/
@[reassoc (attr := simp)]
theorem upper_face_zero : stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u} =
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply CartesianMonoidalCategory.hom_ext
  · change stdSimplex.δ (0 : Fin 2).castSucc ≫ stdSimplex.σ (0 : Fin 2) = 𝟙 _
    exact CosimplicialObject.δ_comp_σ_self SSet.stdSimplex
  · change stdSimplex.δ (0 : Fin 2).castSucc ≫ stdSimplex.σ (0 : Fin 1).succ = _
    rw [CosimplicialObject.δ_comp_σ_of_le SSet.stdSimplex (by decide),
      stdSimplex.δ_zero_eq_const, SSet.comp_const, lift_snd]

/-- 概要：上側の三角形の最後の面は正方形の左辺。
方針：第一射影は始点に定数、第二射影は恒等射となる。
規約：頂点の組は (0,t)。
使われ方：Goerss–Jardine I §7。正方形の境界固定条件。 -/
@[reassoc (attr := simp)]
theorem upper_face_last : stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u} =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  apply CartesianMonoidalCategory.hom_ext
  · change stdSimplex.δ (1 : Fin 2).succ ≫ stdSimplex.σ (0 : Fin 1).castSucc = _
    rw [CosimplicialObject.δ_comp_σ_of_gt SSet.stdSimplex (by decide),
      stdSimplex.δ_one_eq_const, SSet.comp_const, lift_fst]
  · change stdSimplex.δ (1 : Fin 2).succ ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 _
    exact CosimplicialObject.δ_comp_σ_succ SSet.stdSimplex

/-- 概要：下側の三角形の零番目の面は正方形の右辺。
方針：上辺の式の二つの座標を交換する。
規約：頂点の組は (1,t)。
使われ方：Goerss–Jardine I §7。正方形のもう二つの境界の固定条件。 -/
@[reassoc (attr := simp)]
theorem lower_face_zero : stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u} =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_swap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_face_zero]
  rfl

/-- 概要：下側の三角形の最後の面は正方形の下辺。
方針：左辺の式の二つの座標を交換する。
規約：頂点の組は (t,0)。
使われ方：Goerss–Jardine I §7。対角辺以外の全ての辺の固定条件。 -/
@[reassoc (attr := simp)]
theorem lower_face_last : stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u} =
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_swap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_face_last]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
