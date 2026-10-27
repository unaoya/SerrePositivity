module
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.UnconditionalData
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeComparisonCore

/-!
概要：固定 data の cone 評価と、元の実加群延長の全 Hom 比較を同じ end に保持する。
方針：選択された実同型の共役を使い、評価との関手等号を先に証明する。
規約：固定 cell 分解・商上の比較は、この比較から自動的には従わない。
使われ方：固定単位・合成入力の cone レベルの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 固定 cone の実右加群への評価。対象や Hom を選び直さない。 -/
def dgSuspensionConeEvaluation (A : PerfDGInput.{u, max (u + 1) v} R) :
    DGFunctor R (DGKappaCone R A (dgKappaConeInput_unconditional' R A κ hκ))
      (RightModule R A) :=
  (dgFullSubcategoryInclusion R (ModuleCategory R A)
    (dgKappaConeInput_unconditional' R A κ hκ).objects).comp (dgConeModuleForget R A)

/-- 固定した実比較同型を、同じ代表評価に対する全 Hom の閉同型として保持する。 -/
def dgSuspensionConeRepresentativeIso
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    ForgetEnrichment.of (Complex R)
      ((dgSuspensionConeEvaluation R κ hκ A).comp (dgModuleExtension R A B f.down)) ≅
      ForgetEnrichment.of (Complex R)
        ((dgSuspensionUnconditionalMapData R κ hκ f).cone.comp
          (dgSuspensionConeEvaluation R κ hκ B)) :=
  dgModuleStrictImageComparisonIso R A B (dgModuleExtension R A B f.down)
    (dgKappaConeInput_unconditional' R A κ hκ).objects
    (dgKappaConeInput_unconditional' R B κ hκ).objects
    (dgKappaSphereClosureExtensionStrictImage R A B f.down hκ Fact.out)

end SerrePositivity.InfinityCategories
