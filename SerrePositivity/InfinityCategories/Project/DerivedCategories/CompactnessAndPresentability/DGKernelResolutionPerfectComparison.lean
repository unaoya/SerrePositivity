module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKernelResolutionMoritaInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleCompactEquivalence
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Construction
/-!
概要：一般 kernel の実分解の source と replacement の perfect 性を保存・反映する。
方針：元の実主導来比較自然同型と compact 性の輸送を使う。
規約：生の出力の射影性や局所 Hom 平坦性を追加しない。使われ方：β5 e。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ主導来作用による実 kernel の比較。 -/
def dgKernelResolutionClassicalComparisonIso (P : Bimodule R E D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).onHomotopy ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E ≅
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).onHomotopy ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R D ⋙ Morita.kernelDerivedTensorOnBimodule R D E P :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionDerivedComparisonIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) ≪≫
    Functor.isoWhiskerLeft _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeClassicalDerivedFunctorIso R D E (Morita.kernelTensor R D E P)).symm
/-- 同じ主導来作用による実 kernel の比較。 -/
lemma dgKernelResolution_perfect_iff
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence]
    (X : HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P))) :
    modulePerfect R E ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E).obj
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).onHomotopy.obj X)) ↔
    modulePerfect R D ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R D).obj
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).onHomotopy.obj X)) := by
  let K := Morita.kernelDerivedTensorOnBimodule R D E P
  have : (Morita.kernelDerivedTensor R D E
      ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P))).Additive :=
    Morita.kernelBrownActionAdditive R D E _
  have : K.Additive := Functor.additive_of_iso
    (Morita.kernelDerivedTensorOnBimoduleIso R D E (BimoduleCategory.of R E D P))
  have : K.asEquivalence.functor.Additive := by change K.Additive; infer_instance
  have he := (dgKernelResolutionClassicalComparisonIso R D E P).app X
  constructor
  · intro h
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfect_equivalence_iff R D E K.asEquivalence _).mp
    exact (modulePerfect R E).prop_of_iso he h
  · intro h
    have h' := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfect_equivalence_iff R D E K.asEquivalence _).mpr h
    exact (modulePerfect R E).prop_of_iso he.symm h'
/-- 同じ主導来作用による実 kernel の比較。 -/
lemma dgKernelResolution_object_perfect_iff
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence]
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) :
    modulePerfect R E ((moduleToDerived R E).obj
      (ForgetEnrichment.of (Complex R) X.replacement.val)) ↔
    modulePerfect R D ((moduleToDerived R D).obj
      (ForgetEnrichment.of (Complex R) X.source.val)) := by
  let XH := (toHomotopy R _).obj (ForgetEnrichment.of (Complex R) X)
  have he := dgKernelResolution_perfect_iff R D E P XH
  have hE := (moduleToHomotopyDerivedIso R E).app
    (ForgetEnrichment.of (Complex R) X.replacement.val)
  have hD := (moduleToHomotopyDerivedIso R D).app
    (ForgetEnrichment.of (Complex R) X.source.val)
  constructor
  · intro h
    exact (modulePerfect R D).prop_of_iso hD
      (he.mp ((modulePerfect R E).prop_of_iso hE.symm h))
  · intro h
    exact (modulePerfect R E).prop_of_iso hE
      (he.mpr ((modulePerfect R D).prop_of_iso hD.symm h))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
