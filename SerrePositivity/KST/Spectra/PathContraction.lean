module

public import SerrePositivity.KST.Spectra.PathContractionBody

/-!
概要：基点固定の path space の収縮写像と端点。
方針：始点を保つ再パラメータ付けの評価を curry する。
規約：標的の Kan 性は収縮の幾何的構成自体には不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：path space の定数 path から恒等射への収縮。
方針：評価前の収縮を点つき Hom へパラメータ付き curry する。
規約：パラメータは path と時刻の直積。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。path space のホモトピー群。 -/
def pathContraction (Y : PointedSimplicialSet.{u}) :
    (basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u}) ⟶ (basedPathSpace Y).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y (pathContractionBody Y)
    (pathContractionBody_basepoint Y)

/-- 概要：path space の収縮の時刻零は定数 path への定数射。
方針：等化子への包含後に評価の時刻零の式を用いる。
規約：定数射は点つき対象の基点を経由する。
使われ方：Goerss–Jardine I §7。収縮の初端。 -/
theorem pathContraction_zero (Y : PointedSimplicialSet.{u}) :
    (SSet.ι₀ : (basedPathSpace Y).right ⟶ _) ≫ pathContraction Y =
      toUnit (basedPathSpace Y).right ≫ (basedPathSpace Y).hom := by
  apply (cancel_mono (PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)).mp
  rw [Category.assoc, pathContraction, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← MonoidalClosed.curry_natural_left, pathContractionBody_zero, Category.assoc,
    PointedObject.basedHom_basepoint_ι, PointedObject.curry_constant]
  rfl

/-- 概要：path space の収縮の時刻一は恒等射。
方針：評価の時刻一の式と curry・uncurry の逆関係を使う。
規約：全単体次数の射の等式。
使われ方：Goerss–Jardine I §7。収縮の終端。 -/
theorem pathContraction_one (Y : PointedSimplicialSet.{u}) :
    (SSet.ι₁ : (basedPathSpace Y).right ⟶ _) ≫ pathContraction Y = 𝟙 _ := by
  apply (cancel_mono (PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)).mp
  rw [Category.assoc, pathContraction, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← MonoidalClosed.curry_natural_left, pathContractionBody_one, pathEvaluation,
    MonoidalClosed.curry_uncurry, Category.id_comp]

/-- 概要：収縮は定数 path の基点を全時刻で固定する。
方針：定数 path 上の評価を等化子へ包含して計算する。
規約：基点を経由するパラメータ付き定数射として述べる。
使われ方：Goerss–Jardine I §7。基点固定ホモトピーの条件。 -/
theorem pathContraction_constant (Y : PointedSimplicialSet.{u}) :
    (basedPathSpace Y).hom ▷ (Δ[1] : SSet.{u}) ≫ pathContraction Y =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (basedPathSpace Y).hom := by
  apply (cancel_mono (PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)).mp
  rw [Category.assoc, pathContraction, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← MonoidalClosed.curry_natural_left, pathContractionBody_constant, Category.assoc,
    PointedObject.basedHom_basepoint_ι, PointedObject.curry_constant]
  rfl

end

end SerrePositivity.KST.Spectra
