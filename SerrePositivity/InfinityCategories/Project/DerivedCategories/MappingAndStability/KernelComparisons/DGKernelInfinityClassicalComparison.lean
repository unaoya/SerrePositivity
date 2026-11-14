module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedClassicalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelClassicalComparison
/-!
概要：元の一般 kernel ∞ 関手の通常の h 上の作用を、既存の導来 tensor へ照合する。
方針：同じ実出力分解の比較と実 augmentation の主導来比較を合成する。
規約：元の出力の射影性・局所 Hom 平坦性を仮定しない。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ実 kernel ∞ 関手の通常の h と古典的導来 tensor の全関手比較。 -/
def dgKernelDerivedInfinity_classicalIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).toFunctor ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).functor ⋙
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E ≅
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).functor ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R D ⋙ Morita.kernelDerivedTensorOnBimodule R D E P :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_classicalIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) ≪≫
    Functor.isoWhiskerLeft
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).functor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelOutputResolutionClassicalComparisonIso R D E P ≪≫ Functor.associator _ _ _)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
