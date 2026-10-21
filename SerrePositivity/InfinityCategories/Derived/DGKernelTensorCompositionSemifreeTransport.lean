module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionRawFactor
/-!
概要：同じ通常 tensor 比較の半自由制限を型輸送に依存せず回収する。
方針：元の通常 tensor 比較の指定値と実包含・出力分解の厳密式を保つ。
規約：元の比較の定義を変更しない。使われ方：元の導来合成子の K-flat 共通経路計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
  (P : Bimodule R E D) (Q : Bimodule R K E)
/-- 元の半自由制限比較は、同じ通常 tensor 比較の実包含による制限の値を保つ。 -/
lemma dgKernelTensorCompositionSemifreeIso_heq :
    HEq (dgKernelTensorCompositionSemifreeIso R D E K P Q)
      ((dgKernelTensorCompositionNerveIso R D E K P Q).precomp
        (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)))) := by
  simp only [dgKernelTensorCompositionSemifreeIso, Eq.mpr]
  rfl
end SerrePositivity.InfinityCategories
