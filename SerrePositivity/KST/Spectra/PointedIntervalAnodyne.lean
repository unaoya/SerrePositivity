module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointedPointedIntervalAnodyne

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedInterval

/-!
概要：基点つき区間の始点包含の anodyne 性。
方針：一次ホーンと零次標準単体の同型を用いる。
規約：モデル構造の存在を使わず Mathlib のホーン生成 anodyne 性を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3（Tag 00TJ）。path space の全境界充填。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき区間の基点を与える射は anodyne。
方針：単位と Δ[0] の終対象としての同型を零次面の包含に前合成する。
規約：基点は始点の頂点零。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3（Tag 00TJ）。path space の全境界充填。 -/
theorem pointedInterval_basepoint_anodyne : anodyneExtensions _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom := by
  let e : 𝟙_ SSet.{u} ≅ (Δ[0] : SSet.{u}) :=
    isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom = e.hom ≫ stdSimplex.δ (1 : Fin 2) := by
    ext m s
    apply stdSimplex.ext
    intro j
    rfl
  rw [he]
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.interval_zeroFace_anodyne

end

end SerrePositivity.KST.Spectra
