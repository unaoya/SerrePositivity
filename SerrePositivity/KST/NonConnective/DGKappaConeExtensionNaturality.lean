module
public import SerrePositivity.KST.NonConnective.DGKappaConeExtensionDerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedDerivedComparison
public import SerrePositivity.DifferentialGraded.Derived.Functor

/-!
概要：実延長の cone 作用を、元の導来延長との全関手自然性四角形へ接続する。
方針：射影的 cone の augmentation は延長後も準同型であり、正本の導来合成子を適用する。
規約：固定 I・J と strict image を保持し、全入力族の作用の存在は推論しない。
使われ方：K-7 e の任意入力 Morita 射に対する、同じ実 cone 作用の同値判定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [Small.{u} D] (f : DGFunctor R C D)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D (dgModuleExtension R C D f) I.objects J.objects)
local notation "F" => DGFunctor.comp
  (dgFullSubcategoryInclusion R (ModuleCategory R C) I.objects) (dgConeModuleForget R C)

/-- 同じ射影的 cone の出力分解の augmentation は、実延長後も準同型となる。 -/
theorem dgKappaConeExtension_augmentation_quasiIso
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (DGKappaCone R C I) C
      ((dgFullSubcategoryInclusion R (ModuleCategory R C) I.objects).comp
        (dgConeModuleForget R C))) :
    moduleQuasiIso R D ((dgModuleExtension R C D f).onClosed.map X.augmentation) :=
  dgModuleExtension_projective_quasiIso R C D f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R C X.replacement)
    (I.projective X.source.val X.source.property) X.augmentation X.quasiIso

/-- 元の同じ導来包含の後の導来延長を、実 cone 延長の出力分解へ比較する。 -/
def dgKappaConeExtensionDerivedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaConeDerivedComparison R C I ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (DGKappaCone R C I) D
        (dgKappaConeExtensionBimodule R C D f I)) := by
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (DGKappaCone R C I) C F
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (dgKappaConeDerivedComparison R C I) := by
    simpa only [G, dgKappaConeDerivedComparison, dgConeModuleDerived] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R (DGKappaCone R C I) (ModuleCategory R C) C
        (dgFullSubcategoryInclusion R (ModuleCategory R C) I.objects) (dgConeModuleForget R C)
  have e₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_derivedFunctorIso R C D (dgModuleExtension R C D f)
    (fun _ hM => dgModuleExtension_homotopicallyProjective R C D f hM)
  have e₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_compositionIso R (DGKappaCone R C I) C D F
    (dgModuleExtension R C D f) (dgKappaConeExtension_augmentation_quasiIso R C D f I)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e₀.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D f) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e₁.symm G ≪≫ e₂

/-- 同じ実 cone 関手と元の導来延長は、元の二つの導来包含に自然。 -/
def dgKappaConeStrictImageDerivedSquare :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaConeDerivedComparison R C I ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (e.functor R C D _ I.objects J.objects) ≫
        dgKappaConeDerivedComparison R D J) :=
  dgKappaConeExtensionDerivedIso R C D f I ≪≫ dgKappaConeStrictImageDerivedIso R C D f I J e

end SerrePositivity.KST.NonConnective
