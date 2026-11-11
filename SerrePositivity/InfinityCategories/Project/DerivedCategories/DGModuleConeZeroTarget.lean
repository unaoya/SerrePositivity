module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingConeZeroTarget
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
/-!
概要：零を標的とする実 dg 加群の標準 cone は、元の一回 shift に厳密な閉同型で一致する。
方針：既存の複体 cone 接続射の同型性を全評価へ適用し、同じ加群射の同型性を反映する。
規約：主導来圏の同型へ弱めず、元の moduleConeConnecting を同型の順射とする。
使われ方：D-8 c3 の native 懸垂と実 shift の比較、標準 cone の零標的特殊化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 零標的の同じ実 cone 接続射は閉加群同型。 -/
lemma dgModuleConeConnecting_isIso_of_isZero {M N : ModuleCategory R D}
    (f : M ⟶ N) (hN : IsZero N) : IsIso (moduleConeConnecting R D f) := by
  apply moduleIsIso_of_evaluations R D
  intro x
  rw [moduleConeConnecting_eval]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mappingCone_connecting_isIso_of_isZero _ ((moduleEvaluation R D x).map_isZero hN)

/-- 同じ接続射を順射とする、零標的 cone と元の一回 shift の実閉同型。 -/
def dgModuleConeZeroTargetIso {M N : ModuleCategory R D} (f : M ⟶ N) (hN : IsZero N) :
    moduleCone R D f ≅ M⟦(1 : ℤ)⟧ := by
  let := dgModuleConeConnecting_isIso_of_isZero R D f hN
  exact asIso (moduleConeConnecting R D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
