module
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCounitSpaces
public import SerrePositivity.InfinityCategories.Derived.DGKernelResolutionCounit
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ一般 kernel の実出力射影に対する、全写像空間の実普遍余単位。 -/
def dgKernelResolutionUniversalCounit (P : Bimodule R E D) (y : SemifreeDGModules R E) :
    DGUniversalCounit R
      (DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)) (SemifreeDGModules R E)
      (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)) y := by
  apply Classical.choice
  obtain ⟨t, ε, hu⟩ := dgKernelResolutionCounit_quasiIso_exists R D E P y
  exact ⟨⟨t, ε, hu⟩⟩
end SerrePositivity.InfinityCategories
