module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberHomotopyBoundary
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-! # dg 加群の標準 cofiber と fiber の比較辺は同値

概要：明示比較・逆射・両合成の原始元を実際の dg nerve の可逆辺へ昇格する。
方針：一方は厳密な恒等、もう一方は構成済みの全 Hom end のホモトピーを使う。
規約：実射影と cone ホモトピーを保持する。使われ方：β3 の双カルテジアン判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 比較の後の逆射は零原始元によって恒等にホモトピック。 -/
def dgModuleCofiberFiberLiftRetractHomotopy (f : M ⟶ N) :
    ModuleHomotopy A D (dgModuleCofiberFiberLift A D f ≫ dgModuleCofiberFiberRetract A D f)
      (𝟙 M) := by
  rw [dgModuleCofiberFiberLift_retract]
  exact ⟨0, by rw [map_zero, sub_self]⟩

/-- 実比較射と実逆射は全 Hom end のホモトピー商で同型を作る。 -/
def dgModuleCofiberFiberHomotopyIso (f : M ⟶ N) :
    (moduleToHomotopy A D).obj M ≅
      (moduleToHomotopy A D).obj
        (ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f))) :=
  dgModuleHomotopyIsoOfInverse A D (dgModuleCofiberFiberLift A D f)
    (dgModuleCofiberFiberRetract A D f) (dgModuleCofiberFiberLiftRetractHomotopy A D f)
    (dgModuleCofiberFiberRetractLiftHomotopy A D f)

/-- 標準 cofiber の始域から標準 fiber への実比較辺は可逆。 -/
lemma dgModuleCofiberFiberLift_isIso (f : M ⟶ N) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (dgModuleEdge A D (dgModuleCofiberFiberLift A D f)).toTruncated) :=
  dgModuleEdge_isIso_of_inverse A D (dgModuleCofiberFiberLift A D f)
    (dgModuleCofiberFiberRetract A D f) (dgModuleCofiberFiberLiftRetractHomotopy A D f)
    (dgModuleCofiberFiberRetractLiftHomotopy A D f)

/-- 標準比較の実際の辺は ∞ 圏の可逆辺である。 -/
lemma dgModuleCofiberFiberLift_isInvertible (f : M ⟶ N) :
    IsInvertibleEdge (X := dgModuleNerve A D)
      (dgModuleEdge A D (dgModuleCofiberFiberLift A D f)).toTruncated := by
  have := dgModuleCofiberFiberLift_isIso A D f
  exact (edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk
      (dgModuleEdge A D (dgModuleCofiberFiberLift A D f)).toTruncated)

/-- 比較は実閉加群射として元の射影の脚を厳密に保持する。 -/
lemma dgModuleCofiberFiberLift_projection (f : M ⟶ N) :
    dgModuleCofiberFiberLift A D f ≫ dgModuleFiberProjection A D (moduleConeInr A D f) = f := by
  apply dgModuleMorphism_ext_cycle A D
  rw [dgModuleClosedCycle_comp, dgModuleCofiberFiberLift_cycle, dgModuleFiberProjection_cycle]
  exact dgModuleCofiberFiberLift_projection_element A D f

/-- 比較は cone の左包含という実ホモトピーを厳密に保持する。 -/
lemma dgModuleCofiberFiberLift_nullHomotopy (f : M ⟶ N) :
    compose A (dgModuleFiberNullHomotopy A D (moduleConeInr A D f))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (dgModuleCofiberFiberLift A D f))).val
      (zero_add (-1)) = moduleConeInlElement A D f := by
  rw [dgModuleCofiberFiberLift_cycle]
  exact dgModuleCofiberFiberLift_nullHomotopy_element A D f

end SerrePositivity.InfinityCategories
