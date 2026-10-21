module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionReplacementUnlift
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedChangeComparison
public import SerrePositivity.InfinityCategories.Derived.ResolutionOutputPostcompositionTransport
/-!
概要：元の出力分解と変更同型の指定値を、同じ raw 出力射影へ回収する。
方針：出力宇宙の上げ下げと指定出力比較の後合成則だけを使う。
規約：元の入力切断と変更比較を保持。使われ方：導来射作用との共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
variable {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
  (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)))
def dgModuleOutputResolution_rawChangeIso :
    FunctorIso
      ((dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
        dgNerve.map (dgModuleFunctorResolutionReplacement R C E F))
      ((dgModuleFunctorResolutionSourceNerveEquivalence R C E G).inv ≫
        dgNerve.map (dgModuleFunctorResolutionReplacement R C E G)) := by
  have hS := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_sourceLift R C E a hs hq ha)
  have hR := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_replacement R C E a hs hq ha)
  simp only [dgNerve.map_comp] at hS hR
  exact qCatResolutionOutputComparisonIso
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F)
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E G)
    (dgNerve.map (dgModuleResolutionChangeFunctor R C E a hs hq ha))
    (dgNerve.map (dgModuleFunctorResolutionReplacement R C E F))
    (dgNerve.map (dgModuleFunctorResolutionReplacement R C E G)) hS hR
lemma dgModuleOutputResolution_changeIso_down_heq :
    HEq ((dgModuleOutputResolution_changeIso R C E a hs hq ha).postcomp
      (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E))))
      (dgModuleOutputResolution_rawChangeIso R C E a hs hq ha) := by
  have hS := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_sourceLift R C E a hs hq ha)
  have hR := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_replacementLift R C E a hs hq ha)
  have hR' := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_replacement R C E a hs hq ha)
  simp only [dgNerve.map_comp] at hS hR hR'
  unfold dgModuleOutputResolution_changeIso dgModuleOutputResolution_rawChangeIso
  exact qCatResolutionOutputComparisonIso_postcomp_heq_of_outputs
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F)
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E G)
    (dgNerve.map (dgModuleResolutionChangeFunctor R C E a hs hq ha))
    (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F))
    (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E G))
    (dgNerve.map (dgModuleFunctorResolutionReplacement R C E F))
    (dgNerve.map (dgModuleFunctorResolutionReplacement R C E G)) hS hR hR'
    (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E)))
    (dgModuleFunctorResolutionReplacementLift_down R C E F)
    (dgModuleFunctorResolutionReplacementLift_down R C E G)
end SerrePositivity.InfinityCategories
