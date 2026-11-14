module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.Perfect
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.Comparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedChangeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecomposition

/-!
概要：実延長と代表化した cone 関手を、同じ実導来模型への全関手同型で比較する。
方針：全 Hom 自然な実同型を出力分解変更へ送り、同じ元の導来包含を回収する。
規約：strict image を明示入力に保つ。対象別の導来同型や H⁰ 比較で代用しない。
使われ方：K-7 e の実入力射の Morita 判定を、同じ cone・商の比較へ移す。
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

/-- 元の cone 加群を実延長した、同じ未分解出力の双加群。 -/
def dgKappaConeExtensionBimodule : DGFunctor R (DGKappaCone R C I) (RightModule R D) :=
  ((dgFullSubcategoryInclusion R (ModuleCategory R C) I.objects).comp
    (dgConeModuleForget R C)).comp (dgModuleExtension R C D f)

/-- 同じ代表化 cone 関手を元の実加群として評価した双加群。 -/
def dgKappaConeStrictImageBimodule : DGFunctor R (DGKappaCone R C I) (RightModule R D) :=
  (((e.functor R C D _ I.objects J.objects).comp
    (dgFullSubcategoryInclusion R (ModuleCategory R D) J.objects)).comp
      (dgConeModuleForget R D))

/-- 全 Hom 自然な同じ閉同型は、同じ二つの出力分解を全関手で比較する。 -/
def dgKappaConeExtensionResolvedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (DGKappaCone R C I) D
        (dgKappaConeExtensionBimodule R C D f I))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (DGKappaCone R C I) D
        (dgKappaConeStrictImageBimodule R C D f I J e)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso R (DGKappaCone R C I) D
    (F := dgKappaConeExtensionBimodule R C D f I)
    (G := dgKappaConeStrictImageBimodule R C D f I J e)
    (fun M => (e.iso M).hom)
  · intro M
    rw [moduleDegreewiseSurjective_iff_epi]
    intro x n
    infer_instance
  · intro M x
    change QuasiIso ((moduleEvaluation R D x).map (e.iso M).hom)
    infer_instance
  · intro M N
    simpa only [dgKappaConeExtensionBimodule, dgKappaConeStrictImageBimodule,
      DGFunctor.comp, EnrichedFunctor.comp, dgFullSubcategoryInclusion,
      dgConeModuleForget, Category.id_comp, Category.comp_id] using!
        e.comparison_naturality R C D (dgModuleExtension R C D f) I.objects J.objects M N

/-- 代表化した同じ cone 射の後の実導来包含は、元の実延長の出力分解と全関手で同型。 -/
def dgKappaConeStrictImageDerivedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (DGKappaCone R C I) D
        (dgKappaConeExtensionBimodule R C D f I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (e.functor R C D _ I.objects J.objects) ≫
        dgKappaConeDerivedComparison R D J) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R (DGKappaCone R C I)
    (ModuleCategory R D) D
    ((e.functor R C D _ I.objects J.objects).comp
      (dgFullSubcategoryInclusion R (ModuleCategory R D) J.objects)) (dgConeModuleForget R D)
  have h' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (DGKappaCone R C I) D
        (dgKappaConeStrictImageBimodule R C D f I J e))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (e.functor R C D _ I.objects J.objects) ≫
        dgKappaConeDerivedComparison R D J) := by
    simpa only [dgKappaConeStrictImageBimodule, dgKappaConeDerivedComparison,
      dgConeModuleDerived, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using! h
  exact dgKappaConeExtensionResolvedIso R C D f I J e ≪≫ h'

end SerrePositivity.KST.NonConnective
