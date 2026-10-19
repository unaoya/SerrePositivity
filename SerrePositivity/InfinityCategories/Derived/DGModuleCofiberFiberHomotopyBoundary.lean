module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberHomotopy

/-! # cofiber と fiber の比較の実合成と原始元の照合

概要：計算した原始元の微分が実閉加群射の合成と恒等の差であることを証明する。
方針：fiber の二座標を実射影・零ホモトピーとの合成で計算する。
規約：h の抽象的同型を仮定しない。使われ方：β3 の比較辺の明示的 ∞ 同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 実際の逆射の後の比較と恒等の差の原始元。 -/
lemma dgModuleCofiberFiberHomotopyElement_differential (f : M ⟶ N) :
    (moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
      (dgModuleFiber A D (moduleConeInr A D f))).d (-1) 0
        (dgModuleCofiberFiberHomotopyElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (dgModuleCofiberFiberRetract A D f ≫ dgModuleCofiberFiberLift A D f))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (𝟙 (ForgetEnrichment.of (Complex A)
          (dgModuleFiber A D (moduleConeInr A D f)))))).val := by
  let P := ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f))
  let e := dgModuleFiberHomCoordinates A D P (moduleConeInr A D f) (-1)
  have hp : (e (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
      (dgModuleCofiberFiberRetract A D f ≫ dgModuleCofiberFiberLift A D f))).val).1 =
      compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
        (dgModuleCofiberFiberRetractElement A D f) (zero_add 0) := by
    rw [dgModuleFiberHomCoordinates_fst, dgModuleClosedCycle_comp,
      dgModuleCofiberFiberRetract_cycle, dgModuleCofiberFiberLift_cycle,
      compose_assoc, dgModuleCofiberFiberLift_projection_element]
  have hh : (e (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
      (dgModuleCofiberFiberRetract A D f ≫ dgModuleCofiberFiberLift A D f))).val).2 =
      compose A (moduleConeInlElement A D f) (dgModuleCofiberFiberRetractElement A D f)
        (zero_add (-1)) := by
    rw [dgModuleFiberHomCoordinates_snd, dgModuleClosedCycle_comp,
      dgModuleCofiberFiberRetract_cycle, dgModuleCofiberFiberLift_cycle,
      compose_assoc, dgModuleCofiberFiberLift_nullHomotopy_element]
  have hip : (e (unitElement A (ForgetEnrichment.to (Complex A) P)).val).1 =
      dgModuleFiberProjectionElement A D (moduleConeInr A D f) := by
    rw [dgModuleFiberHomCoordinates_fst, compose_unit]
  have hih : (e (unitElement A (ForgetEnrichment.to (Complex A) P)).val).2 =
      dgModuleFiberNullHomotopy A D (moduleConeInr A D f) := by
    rw [dgModuleFiberHomCoordinates_snd, compose_unit]
  dsimp only [P] at hip hih
  apply e.injective
  rw [dgModuleCofiberFiberHomotopyElement_differential_coordinates,
    LinearEquiv.apply_symm_apply, dgModuleClosedCycle_id, map_sub]
  apply Prod.ext
  · exact (congrArg₂ (fun a b => a - b) hp hip).symm
  · refine Eq.trans ?_ (congrArg₂ (fun a b => a - b) hh hih).symm
    have hd := dgModuleCofiberFiberContractionN_decomposition A D f
    rw [← hd]
    abel_nf

/-- 次数 −1 の実原始元を閉加群射のホモトピーとして保持する。 -/
def dgModuleCofiberFiberRetractLiftHomotopy (f : M ⟶ N) :
    ModuleHomotopy A D (dgModuleCofiberFiberRetract A D f ≫ dgModuleCofiberFiberLift A D f)
      (𝟙 _) :=
  ⟨dgModuleCofiberFiberHomotopyElement A D f,
    dgModuleCofiberFiberHomotopyElement_differential A D f⟩

end SerrePositivity.InfinityCategories
