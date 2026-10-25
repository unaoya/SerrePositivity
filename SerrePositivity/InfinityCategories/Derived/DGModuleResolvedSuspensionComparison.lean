module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedConeSquares
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeZeroTarget
public import SerrePositivity.InfinityCategories.Stable.SuspensionEquivalence
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet Pretriangulated
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 零への標準 cone は、主導来像で元の一回 shift と同型。 -/
def dgModuleConeToZeroDerivedShiftIso (M : ModuleCategory R D) :
    (moduleToDerived R D).obj (moduleCone R D (moduleToZero R D M)) ≅
      (moduleToDerived R D).obj (M⟦(1 : ℤ)⟧) :=
  (moduleToDerived R D).mapIso
    (dgModuleConeZeroTargetIso R D (moduleToZero R D M) (moduleZero_isZero R D))

/-- 同じ実導来 cone 頂点と同じ shift 加群頂点の native 同型。 -/
def dgConeModuleDerivedConeToZeroShiftIso (M : ModuleCategory R D) :
    VertexIso (dgConeModuleDerivedVertex R D (moduleCone R D (moduleToZero R D M)))
      (dgConeModuleDerivedVertex R D (M⟦(1 : ℤ)⟧)) :=
  dgConeModuleDerivedVertexIsoOfDerivedIso R D (dgModuleConeToZeroDerivedShiftIso R D M)

/-- native 懸垂の自己同値の値は、元の同じ一回 shift 加群の実導来頂点に同型。 -/
def dgConeModuleDerivedShiftOneSuspensionIso (M : ModuleCategory R D) :
    letI := dgModuleDerivedInfinityCategory_isStable R D
    (suspensionFunctor (dgModuleDerivedInfinityCategory R D)).obj
      (SSet.HomotopyCategory.mk (dgConeModuleDerivedVertex R D M)) ≅
        SSet.HomotopyCategory.mk (dgConeModuleDerivedVertex R D (M⟦(1 : ℤ)⟧)) := by
  let := dgModuleDerivedInfinityCategory_isStable R D
  let s := dgConeModuleDerivedSuspensionSquare R D M
  have he : s.vertex =
      dgConeModuleDerivedVertex R D (moduleCone R D (moduleToZero R D M)) :=
    dgConeModuleDerived_coneSquare_vertex R D _
  exact s.suspensionFunctorObjIso ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk he) ≪≫
    dgConeModuleDerivedConeToZeroShiftIso R D M

end SerrePositivity.InfinityCategories
