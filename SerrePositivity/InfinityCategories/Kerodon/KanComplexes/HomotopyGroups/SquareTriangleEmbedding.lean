module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTriangles

/-!
概要：正方形の二つの三角形の包含の単射性。
方針：二つの退化写像の値の和から元の頂点を復元する。
規約：全ての単体次数で単射性を検査する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形の三角形の pushout 表示。

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

/-- 概要：二つの退化写像の頂点の値の和は元の三角形の頂点の値。
方針：三つの頂点で計算する。
規約：添字は σ₀ と σ₁。
使われ方：Goerss–Jardine I §7。三角形の包含の単射性。 -/
theorem sigma_values_sum (a : Fin 3) :
    ((SimplexCategory.σ (0 : Fin 2)) a).val +
      ((SimplexCategory.σ (1 : Fin 2)) a).val = a.val := by
  fin_cases a <;> rfl

/-- 概要：上側の三角形の包含は各単体次数で単射。
方針：二つの成分の値の和で元の単体の全頂点を復元する。
規約：d は任意の単体次数。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形の三角形の貼り合わせ。 -/
theorem upper_app_injective (d : ℕ) : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u}.app (Opposite.op ⦋d⦌)) := by
  intro s t h
  apply stdSimplex.ext
  intro r
  apply Fin.ext
  have h₀ := congrArg (fun a => (a.1 r).val) h
  have h₁ := congrArg (fun a => (a.2 r).val) h
  change ((SimplexCategory.σ (0 : Fin 2)) (s r)).val =
    ((SimplexCategory.σ (0 : Fin 2)) (t r)).val at h₀
  change ((SimplexCategory.σ (1 : Fin 2)) (s r)).val =
    ((SimplexCategory.σ (1 : Fin 2)) (t r)).val at h₁
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sigma_values_sum (s r)
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sigma_values_sum (t r)
  omega

/-- 概要：正方形の上側の三角形への射は単射。
方針：各単体次数の単射性から自然変換の単射性を得る。
規約：通常の単体集合の単射。
使われ方：Goerss–Jardine I §7。正方形の pushout の検査。 -/
instance upper_mono : Mono _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u} := by
  have : ∀ m, Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper.{u}.app m) := by
    intro ⟨⟨d⟩⟩
    exact (mono_iff_injective _).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_app_injective d)
  exact NatTrans.mono_of_mono_app _

/-- 概要：正方形の下側の三角形への射も単射。
方針：上側の包含と座標の交換同型の合成として表す。
規約：通常の単体集合の単射。
使われ方：Goerss–Jardine I §7。正方形の二つの三角形の対称的な貼り合わせ。 -/
instance lower_mono : Mono _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower.{u} := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_swap]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_mono (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareTriangles.lower_mono := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_mono

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareTriangles.sigma_values_sum := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.sigma_values_sum

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareTriangles.upper_app_injective := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_app_injective

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_mono (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareTriangles.upper_mono := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_mono
