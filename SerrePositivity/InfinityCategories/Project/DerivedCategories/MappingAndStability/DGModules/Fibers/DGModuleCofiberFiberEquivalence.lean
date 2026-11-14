module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleCofiberFiberHomotopyBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # dg 加群の標準 cofiber と fiber の比較辺は同値

概要：明示比較・逆射・両合成の原始元を実際の dg nerve の可逆辺へ昇格する。
方針：一方は厳密な恒等、もう一方は構成済みの全 Hom end のホモトピーを使う。
規約：実射影と cone ホモトピーを保持する。使われ方：β3 の双カルテジアン判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 比較の後の逆射は零原始元によって恒等にホモトピック。 -/
def dgModuleCofiberFiberLiftRetractHomotopy (f : M ⟶ N) :
    ModuleHomotopy A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract A D f)
      (𝟙 M) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_retract]
  exact ⟨0, by rw [map_zero, sub_self]⟩

/-- 実比較射と実逆射は全 Hom end のホモトピー商で同型を作る。 -/
def dgModuleCofiberFiberHomotopyIso (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).obj M ≅
      (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).obj
        (ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyIsoOfInverse A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract A D f) (dgModuleCofiberFiberLiftRetractHomotopy A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetractLiftHomotopy A D f)

/-- 標準 cofiber の始域から標準 fiber への実比較辺は可逆。 -/
lemma dgModuleCofiberFiberLift_isIso (f : M ⟶ N) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)).toTruncated) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_inverse A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract A D f) (dgModuleCofiberFiberLiftRetractHomotopy A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetractLiftHomotopy A D f)

/-- 標準比較の実際の辺は ∞ 圏の可逆辺である。 -/
lemma dgModuleCofiberFiberLift_isInvertible (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)).toTruncated := by
  have := dgModuleCofiberFiberLift_isIso A D f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)).toTruncated)

/-- 比較は実閉加群射として元の射影の脚を厳密に保持する。 -/
lemma dgModuleCofiberFiberLift_projection (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D (moduleConeInr A D f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleMorphism_ext_cycle A D
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_cycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_projection_element A D f

/-- 比較は cone の左包含という実ホモトピーを厳密に保持する。 -/
lemma dgModuleCofiberFiberLift_nullHomotopy (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f))).val
      (zero_add (-1)) = moduleConeInlElement A D f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_cycle]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_nullHomotopy_element A D f

end SerrePositivity.InfinityCategories.Project.DerivedCategories
