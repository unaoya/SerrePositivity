module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompInfinity
public import SerrePositivity.InfinityCategories.Derived.ResolutionOutputPrecomposition
/-!
概要：入力前合成に沿う、元の実半自由出力分解 ∞ 関手の全関手同型。
方針：同じ全 Hom・実二射影・比較 cochain の等式を保持して構成する。
規約：元の出力の射影性と入力の小ささは不要。使われ方：二変数 Hom の固定入力制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve MonoidalCategory
open CochainComplex HomComplex SSet
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 任意の入力 dg 関手の前合成に沿う、元の実出力 ∞ 関手の全関手同型。 -/
def dgModuleOutputResolution_precompIso :
    FunctorIso (dgModuleOutputResolutionInfinity R A E (H.comp F))
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) ≫
        dgModuleOutputResolutionInfinity R C E F) := by
  have hs := congrArg (fun G => dgNerve.map G)
    (dgModuleResolutionPrecompFunctor_sourceLift R A C E H F)
  have hr := congrArg (fun G => dgNerve.map G)
    (dgModuleResolutionPrecompFunctor_replacementLift R A C E H F)
  simp only [dgNerve.map_comp] at hs hr
  exact qCatResolutionOutputPrecompIso
    (dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F))
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F)
    _ (dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F))
    (dgNerve.map (dgModuleFunctorResolutionReplacementLift R A E (H.comp F)))
    (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F)) hs hr
end SerrePositivity.InfinityCategories
