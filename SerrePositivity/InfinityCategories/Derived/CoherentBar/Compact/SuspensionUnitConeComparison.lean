module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeRepresentativeComparison

/-!
概要：固定恒等 data の cone 作用を、全 Hom 自然な実比較で恒等作用と照合する。
方針：代表化の共役同型と、実加群延長の恒等比較を合成する。
規約：固定 cell 分解・商の関手圏への持ち上げは、この比較とは別の問題である。
使われ方：固定入力の単位比較の不足箇所を正確に切り分ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 代表の共役と恒等延長比較を、全 Hom 自然な閉同型として合成する。 -/
def dgSuspensionUnitConeEvaluationIso :
    ForgetEnrichment.of (Complex R)
      ((dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).cone.comp
        (dgSuspensionConeEvaluation R κ hκ A)) ≅
      ForgetEnrichment.of (Complex R) (dgSuspensionConeEvaluation R κ hκ A) :=
  (dgSuspensionConeRepresentativeIso R κ hκ (𝟙 A)).symm ≪≫
    dgModuleIdentityPrecompositionIso R A (dgSuspensionConeEvaluation R κ hκ A)

end SerrePositivity.InfinityCategories
