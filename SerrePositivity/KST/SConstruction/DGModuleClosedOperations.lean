module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModulePropertyChoices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BicartesianCriterion

/-! # dg 加群の実有限操作に閉じた対象条件
概要：実零加群・cone・fiber に閉じた対象条件を束ねる。
方針：H⁰ の三角構造を仮定せず、元の加群の対象で閉性を述べる。
規約：部分圏の安定性を入力としない。使われ方：射影的 perfect dg 加群の安定性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実零対象と標準 cone・fiber に閉じた、全 dg 加群上の対象条件。 -/
structure DGModuleClosedOperations (P : RightModule A D → Prop) : Prop where
  zero_mem : P (zeroModule A D)
  cone_mem {M N : ModuleCategory A D} (f : M ⟶ N) :
    P (ForgetEnrichment.to (Complex A) M) → P (ForgetEnrichment.to (Complex A) N) →
      P (ForgetEnrichment.to (Complex A) (moduleCone A D f))
  fiber_mem {M N : ModuleCategory A D} (f : M ⟶ N) :
    P (ForgetEnrichment.to (Complex A) M) → P (ForgetEnrichment.to (Complex A) N) →
      P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)

end SerrePositivity.KST.SConstruction
