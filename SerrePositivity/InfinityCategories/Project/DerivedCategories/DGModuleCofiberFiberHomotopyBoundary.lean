module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberFiberHomotopy

/-! # cofiber と fiber の比較の実合成と原始元の照合

概要：計算した原始元の微分が実閉加群射の合成と恒等の差であることを証明する。
方針：fiber の二座標を実射影・零ホモトピーとの合成で計算する。
規約：h の抽象的同型を仮定しない。使われ方：β3 の比較辺の明示的 ∞ 同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 実際の逆射の後の比較と恒等の差の原始元。 -/
lemma dgModuleCofiberFiberHomotopyElement_differential (f : M ⟶ N) :
    (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))).d (-1) 0
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberHomotopyElement A D f) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)))))).val := by
  let P := ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D P (moduleConeInr A D f) (-1)
  have hp : (e (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f))).val).1 =
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetractElement A D f) (zero_add 0) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract_cycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_cycle,
      compose_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_projection_element]
  have hh : (e (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f))).val).2 =
      compose A (moduleConeInlElement A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetractElement A D f)
        (zero_add (-1)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract_cycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_cycle,
      compose_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_nullHomotopy_element]
  have hip : (e (_root_.SerrePositivity.DifferentialGraded.unitElement A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) P)).val).1 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_fst, compose_unit]
  have hih : (e (_root_.SerrePositivity.DifferentialGraded.unitElement A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) P)).val).2 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_snd, compose_unit]
  dsimp only [P] at hip hih
  apply e.injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberHomotopyElement_differential_coordinates,
    LinearEquiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_id, map_sub]
  apply Prod.ext
  · exact (congrArg₂ (fun a b => a - b) hp hip).symm
  · refine Eq.trans ?_ (congrArg₂ (fun a b => a - b) hh hih).symm
    have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN_decomposition A D f
    rw [← hd]
    abel_nf

/-- 次数 −1 の実原始元を閉加群射のホモトピーとして保持する。 -/
def dgModuleCofiberFiberRetractLiftHomotopy (f : M ⟶ N) :
    ModuleHomotopy A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetract A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)
      (𝟙 _) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberHomotopyElement A D f,
    dgModuleCofiberFiberHomotopyElement_differential A D f⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
