module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedConeSquares
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeZeroTarget
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalence
/-!
概要：実加群の一回 shift と、同じ実導来頂点の native 懸垂を比較する。
方針：零への標準 cone の実閉接続同型を、同じ実導来 cone の懸垂四角形へ戻す。
規約：比較は頂点同型であり、固定模型上の厳密豊穣 shift 作用を主張しない。
使われ方：D-8 c3。native 自己同値による κ-compact 性保存との接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet Pretriangulated
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 零への標準 cone は、主導来像で元の一回 shift と同型。 -/
def dgModuleConeToZeroDerivedShiftIso (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj (_root_.SerrePositivity.DifferentialGraded.moduleCone R D (_root_.SerrePositivity.DifferentialGraded.moduleToZero R D M)) ≅
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj (M⟦(1 : ℤ)⟧) :=
  (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTargetIso R D (moduleToZero R D M) (moduleZero_isZero R D))

/-- 同じ実導来 cone 頂点と同じ shift 加群頂点の native 同型。 -/
def dgConeModuleDerivedConeToZeroShiftIso (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D (moduleCone R D (moduleToZero R D M)))
      (dgConeModuleDerivedVertex R D (M⟦(1 : ℤ)⟧)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso R D (dgModuleConeToZeroDerivedShiftIso R D M)

/-- native 懸垂の自己同値の値は、元の同じ一回 shift 加群の実導来頂点に同型。 -/
def dgConeModuleDerivedShiftOneSuspensionIso (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R D
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).obj
      (SSet.HomotopyCategory.mk (dgConeModuleDerivedVertex R D M)) ≅
        SSet.HomotopyCategory.mk (dgConeModuleDerivedVertex R D (M⟦(1 : ℤ)⟧)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R D
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedSuspensionSquare R D M
  have he : s.vertex =
      dgConeModuleDerivedVertex R D (_root_.SerrePositivity.DifferentialGraded.moduleCone R D (_root_.SerrePositivity.DifferentialGraded.moduleToZero R D M)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerived_coneSquare_vertex R D _
  exact s.suspensionFunctorObjIso ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk he) ≪≫
    dgConeModuleDerivedConeToZeroShiftIso R D M

end SerrePositivity.InfinityCategories.Project.DerivedCategories
