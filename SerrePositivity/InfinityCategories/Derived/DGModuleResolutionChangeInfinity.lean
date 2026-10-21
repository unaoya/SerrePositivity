module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeFunctor
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionInfinity
public import SerrePositivity.InfinityCategories.Derived.ResolutionProjectionComparison
/-!
概要：全 Hom 自然な次数別全射準同型に沿う、元の実出力分解 ∞ 関手の全関手比較。
方針：同じ比較 dg 関手の両射影の厳密等式と、同じ入力同値の指定逆を使う。
規約：元の出力の射影性・入力の小ささを仮定しない。使われ方：一般双加群の準同型比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
    (ForgetEnrichment.of (Complex R) (G.obj y)))
/-- 対象宇宙を持ち上げた同じ実入力射影も厳密に保存する。 -/
lemma dgModuleResolutionChangeFunctor_sourceLift :
    (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionSourceLift R C E G) =
        dgModuleFunctorResolutionSourceLift R C E F := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionSourceLift R C E G))
    (G := dgModuleFunctorResolutionSourceLift R C E F) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionChangeFunctor,
    dgModuleFunctorResolutionSourceLift, dgModuleFunctorResolutionSource,
    dgUniverseLiftUp, eqToHom_refl, Category.comp_id]
  exact dgModuleResolutionChangeHom_source R C E a hs hq ha X Y
/-- 対象宇宙を持ち上げた同じ実半自由出力射影も厳密に保存する。 -/
lemma dgModuleResolutionChangeFunctor_replacementLift :
    (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionReplacementLift R C E G) =
        dgModuleFunctorResolutionReplacementLift R C E F := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionChangeFunctor R C E a hs hq ha).comp
      (dgModuleFunctorResolutionReplacementLift R C E G))
    (G := dgModuleFunctorResolutionReplacementLift R C E F) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionChangeFunctor,
    dgModuleFunctorResolutionReplacementLift, dgModuleFunctorResolutionReplacement,
    dgUniverseLiftUp, eqToHom_refl, Category.comp_id]
  exact dgModuleResolutionChangeHom_replacement R C E a hs hq ha X Y
/-- 同じ分解変更の実 dg nerve 関手は、両入力射影の同値から実同値となる。 -/
lemma dgModuleResolutionChangeNerve_isQCatEquivalence :
    IsQCatEquivalence (dgNerve.map (dgModuleResolutionChangeFunctor R C E a hs hq ha)) := by
  apply (dgModuleFunctorResolutionSourceNerve_isQCatEquivalence R C E G).cancel_right
  have h := congrArg (fun H => dgNerve.map H)
    (dgModuleResolutionChangeFunctor_sourceLift R C E a hs hq ha)
  simp only [dgNerve.map_comp] at h
  rw [h]
  exact dgModuleFunctorResolutionSourceNerve_isQCatEquivalence R C E F
/-- 同じ指定切断から作る二つの実出力分解 ∞ 関手の全関手同型。 -/
def dgModuleOutputResolution_changeIso :
    FunctorIso (dgModuleOutputResolutionInfinity R C E F)
      (dgModuleOutputResolutionInfinity R C E G) := by
  have hs' := congrArg (fun H => dgNerve.map H)
    (dgModuleResolutionChangeFunctor_sourceLift R C E a hs hq ha)
  have hr' := congrArg (fun H => dgNerve.map H)
    (dgModuleResolutionChangeFunctor_replacementLift R C E a hs hq ha)
  simp only [dgNerve.map_comp] at hs' hr'
  exact qCatResolutionOutputComparisonIso
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F)
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E G)
    (dgNerve.map (dgModuleResolutionChangeFunctor R C E a hs hq ha))
    (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F))
    (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E G)) hs' hr'
end SerrePositivity.InfinityCategories
