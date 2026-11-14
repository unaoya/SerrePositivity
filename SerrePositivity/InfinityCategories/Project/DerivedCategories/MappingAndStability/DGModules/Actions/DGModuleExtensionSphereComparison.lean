module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorShiftIso
public import SerrePositivity.DifferentialGraded.Module.Functor
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import Mathlib.CategoryTheory.Adjunction.Limits
/-!
概要：dg 加群の延長と、ラベル付き自由 sphere の評価を比較する。
方針：次数零の単位比較・実 shift 比較・代表加群の延長比較を合成する。
規約：同型を構成し、関手引数の厳密合成や全高次作用は別に検証する。
使われ方：κ-small な自由表示の Hom 作用を元の延長から移す試作の基盤。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

/-- 次数零の自由 sphere は同じ代表加群と同型。 -/
def dgFreeSphereZeroIso (x : D) :
    freeSphere R D x 0 ≅ ForgetEnrichment.of (Complex R) (representable R x) :=
  moduleTensorUnitIso R D (representable R x)

/-- 任意次数の自由 sphere を代表加群の同じ実 shift と比較する。 -/
def dgFreeSphereShiftedRepresentableIso (x : D) (n : ℤ) :
    freeSphere R D x n ≅
      (ForgetEnrichment.of (Complex R) (representable R x))⟦-n⟧ :=
  (freeSphereShiftIso R D x 0 (-n) ≪≫
    eqToIso (congrArg (freeSphere R D x) (by omega))).symm ≪≫
      (shiftFunctor (ModuleCategory R D) (-n)).mapIso (dgFreeSphereZeroIso R D x)

/-- 延長後の自由 sphere と、写した同じ対象ラベルの自由 sphere の実比較。 -/
def dgModuleExtensionFreeSphereIso (x : D) (n : ℤ) :
    (dgModuleExtension R D E F).onClosed.obj (freeSphere R D x n) ≅
      freeSphere R E (F.obj x) n :=
  (dgModuleExtension R D E F).onClosed.mapIso
      (dgFreeSphereShiftedRepresentableIso R D x n) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorShiftIso R D E (dgModuleExtension R D E F) (-n) (representable R x) ≪≫
    (shiftFunctor (ModuleCategory R E) (-n)).mapIso
      (dgModuleExtensionRepresentableIso R D E F x) ≪≫
    (dgFreeSphereShiftedRepresentableIso R E (F.obj x) n).symm

/-- 元の延長の左随伴性による小さい余積の保存。 -/
lemma dgModuleExtension_preservesColimits :
    PreservesColimitsOfSize.{u, u} (dgModuleExtension R D E F).onClosed :=
  (dgModuleExtensionRestrictionAdjunction R D E F).leftAdjoint_preservesColimits

end SerrePositivity.InfinityCategories.Project.DerivedCategories
