module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberSection
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeTargetHomExt

/-! # 双対比較の実合成と原始元の照合

概要：次数 −1 元の微分を降下比較の後の逆射と恒等の差と同定する。
方針：cone の二射影で比較し、fiber の分解恒等式を第一座標へ代入する。
規約：実閉加群射と全 Hom end の原始元。使われ方：β3 の双対比較辺の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 原始元の微分は降下の後の逆射と恒等の実閉零成分の差。 -/
lemma dgModuleFiberCofiberHomotopyElement_differential (f : M ⟶ N) :
    (moduleHom A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))).d (-1) 0
        (dgModuleFiberCofiberHomotopyElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (dgModuleFiberCofiberDesc A D f ≫ dgModuleFiberCofiberSection A D f))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (𝟙 (moduleCone A D (dgModuleFiberProjection A D f))))).val := by
  have hp : compose A (moduleConeFstElement A D (dgModuleFiberProjection A D f))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (dgModuleFiberCofiberDesc A D f ≫ dgModuleFiberCofiberSection A D f))).val (zero_add 1) =
      compose A (dgModuleFiberCofiberSectionFirst A D f)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
          (dgModuleFiberCofiberDesc A D f))).val (zero_add 1) := by
    rw [dgModuleClosedCycle_comp, dgModuleFiberCofiberSection_cycle,
      compose_assoc, dgModuleFiberCofiberSection_fst]
  have hH := compose_assoc_of_sum (A := A)
    (moduleConeFstElement A D (dgModuleFiberProjection A D f))
    (dgModuleFiberNullHomotopy A D f) (dgModuleFiberCofiberSectionFirst A D f)
    (show 1 + (-1) = 0 by decide) (show (-1) + 1 = 0 by decide)
    (show 1 + (-1) + 1 = 1 by decide)
  have hF := compose_assoc_of_sum (A := A)
    (moduleConeSndElement A D (dgModuleFiberProjection A D f))
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
    (dgModuleFiberCofiberSectionFirst A D f) (zero_add 0) (zero_add 1) (zero_add 1)
  have hT := compose_assoc_of_sum (A := A)
    (moduleConeFstElement A D (dgModuleFiberProjection A D f))
    (dgModuleFiberProjectionElement A D f) (dgModuleFiberCofiberContractionT A D f)
    (add_zero 1) (zero_add 0) (add_zero 1)
  have hd : compose A
      (compose A (dgModuleFiberCofiberSectionFirst A D f) (dgModuleFiberNullHomotopy A D f)
        (show (-1) + 1 = 0 by decide))
      (moduleConeFstElement A D (dgModuleFiberProjection A D f)) (add_zero 1) +
      compose A
      (compose A (dgModuleFiberCofiberContractionT A D f) (dgModuleFiberProjectionElement A D f)
        (zero_add 0))
      (moduleConeFstElement A D (dgModuleFiberProjection A D f)) (add_zero 1) =
      moduleConeFstElement A D (dgModuleFiberProjection A D f) := by
    rw [← compose_add_left, dgModuleFiberCofiberSectionFirst_decomposition, unit_compose]
  apply dgModuleConeTargetHom_ext A D (dgModuleFiberProjection A D f) 0
  · rw [dgModuleFiberCofiberHomotopyElement_differential_coordinates,
      dgModuleConeLiftElement_fst, compose_sub_right, hp, dgModuleClosedCycle_id, compose_unit,
      dgModuleFiberCofiberHomotopyFirst_differential, dgModuleFiberCofiberDesc_cycle,
      dgModuleConeDescElement, compose_add_right, hH, hF, hT]
    have hs (a b c d : GradedHom A
        (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
        (dgModuleFiber A D f) 1) (h : c + b = d) : -(-a + b) = c + a - d := by
      rw [← h]
      abel
    exact hs _ _ _ _ hd
  · rw [dgModuleFiberCofiberHomotopyElement_differential_coordinates,
      dgModuleConeLiftElement_snd, compose_sub_right, dgModuleClosedCycle_comp,
      dgModuleFiberCofiberSection_cycle, compose_assoc, dgModuleFiberCofiberSection_snd,
      zero_compose, dgModuleClosedCycle_id, compose_unit, zero_sub]

/-- 実原始元を閉加群射のホモトピーとして保持する。 -/
def dgModuleFiberCofiberDescSectionHomotopy (f : M ⟶ N) :
    ModuleHomotopy A D (dgModuleFiberCofiberDesc A D f ≫ dgModuleFiberCofiberSection A D f)
      (𝟙 _) :=
  ⟨dgModuleFiberCofiberHomotopyElement A D f,
    dgModuleFiberCofiberHomotopyElement_differential A D f⟩

end SerrePositivity.InfinityCategories
