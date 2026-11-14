module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalCounitSpaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelResolutionCounit
/-!
概要：一般 kernel の同じ実分解の余単位を、全 Hom 空間の普遍性を持つデータにまとめる。
方針：実閉余単位の全整数次数の準同型性から、同じ pinched 写像の同値性を回収する。
規約：実右随伴の coherent な全関手構成は別工程。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ一般 kernel の実出力射影に対する、全写像空間の実普遍余単位。 -/
def dgKernelResolutionUniversalCounit (P : Bimodule R E D) (y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) y := by
  apply Classical.choice
  obtain ⟨t, ε, hu⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionCounit_quasiIso_exists R D E P y
  exact ⟨⟨t, ε, hu⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
