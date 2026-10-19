module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberObject

/-! # shifted cone の射影の合成を零にする全 Hom end のホモトピー

概要：標準 nullhomotopy の微分が射影と元の加群射の合成に等しい。
方針：第二射影の微分と shift 単位の閉性に通常順の Leibniz 則を使う。
規約：符号を含む実際の次数 −1 成分で主張する。使われ方：β3 の fiber 四角形の二単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 標準 nullhomotopy の微分は fiber 射影と元の閉加群射の合成の成分。 -/
lemma dgModuleFiberNullHomotopy_differential (f : M ⟶ N) :
    (moduleHom A D (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N)).d (-1) 0
      (dgModuleFiberNullHomotopy A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (dgModuleFiberProjection A D f ≫ f))).val := by
  rw [dgModuleClosedCycle_comp A D, dgModuleFiberProjection_cycle]
  change differential A (dgModuleFiberNullHomotopy A D f) = _
  rw [dgModuleFiberNullHomotopy, show differential (D := RightModule A D) A
      (-compose A (moduleConeSndElement A D f)
        (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
        (by decide)) =
      -differential A (compose A (moduleConeSndElement A D f)
        (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
        (by decide)) from map_neg _ _, differential_compose]
  have hsnd : differential (D := RightModule A D) A (moduleConeSndElement A D f) =
      -compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
        (moduleConeFstElement A D f) (add_zero 1) := dgModuleConeSndElement_d A D f
  have hout : differential (D := RightModule A D) A
      (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f))) = 0 :=
    moduleShiftOutElement_d A D (-1) _
  rw [hsnd, hout, compose_zero, smul_zero, add_zero]
  have hneg := compose_sub_left (A := A)
    (0 : GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) N) 1)
    (compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
      (moduleConeFstElement A D f) (add_zero 1))
    (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
    (show (-1) + 1 = 0 by decide)
  simp only [zero_sub, zero_compose] at hneg
  rw [hneg, neg_neg]
  exact (compose_assoc A
    (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
    (moduleConeFstElement A D f)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
      (show (-1) + 1 + 0 = 0 by decide)).symm

end SerrePositivity.InfinityCategories
