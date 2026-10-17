module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarGradedSplit
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomNaturality
public import SerrePositivity.DifferentialGraded.Endomorphism.ShortExactComparison
public import SerrePositivity.DifferentialGraded.Module.GradedSplitHomExact

/-! # 全次数で分裂するHom短完全列の実際の係数変更比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

namespace ModuleGradedSplit
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- Homの次数ごとのsectionを線形射として保持する。chain map条件は課さない。 -/
def homRestrictionSectionLinear (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) T)).X q ⟶
      (moduleHom A D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)).X q :=
  ModuleCat.ofHom {
    toFun := s.homRestrictionSection T q
    map_add' a b := by simp only [homRestrictionSection, forward, TensorProduct.tmul_add, map_add]
    map_smul' c a := by
      simp only [homRestrictionSection, forward, TensorProduct.tmul_smul, map_smul]
      rfl }

def homShortComplexDegreewiseSplitting (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ) :
    ((s.homShortComplex T).map (HomologicalComplex.eval (ModuleCat A) (.up ℤ) q)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (s.homShortComplex_degreewise_shortExact T q).exact
    (s.homRestrictionSectionLinear D T q) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact s.homRestriction_section T q z)
    (s.homShortComplex_degreewise_shortExact T q).mono_f

lemma scalarHomShortComplex_shortExact (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) :
    ((s.homShortComplex T).map (ScalarExtension.extension φ)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q =>
    ((s.homShortComplexDegreewiseSplitting D T q).map (ModuleCat.extendScalars φ)).shortExact)

end ModuleGradedSplit

def scalarModuleHomShortComplex {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    (s.homShortComplex T).map (ScalarExtension.extension φ) ⟶
      (scalarModuleGradedSplit φ D s).homShortComplex
        ((ScalarExtension.moduleExtension φ D).obj T) where
  τ₁ := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) T)
  τ₂ := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)
  τ₃ := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) T)
  comm₁₂ := (scalarModuleHom_precompose φ D g T).symm
  comm₂₃ := (scalarModuleHom_precompose φ D f T).symm

lemma scalarModuleHom_gradedSplit_middle {M N P : ModuleCategory A D}
    {f : M ⟶ N} {g : N ⟶ P} (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (hP : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)))
    (hM : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)) :=
  complexQuasiIso_middle_of_shortExact (scalarModuleHomShortComplex φ D s T)
    (s.scalarHomShortComplex_shortExact φ D T)
    ((scalarModuleGradedSplit φ D s).homShortComplex_shortExact
      ((ScalarExtension.moduleExtension φ D).obj T)) hP hM

end SerrePositivity.DifferentialGraded
