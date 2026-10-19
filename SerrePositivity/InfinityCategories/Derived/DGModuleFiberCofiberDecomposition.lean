module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberContraction

/-! # fiber の cofiber 比較の二成分の分解恒等式

概要：逆射の第一成分と零ホモトピー、T と射影の合成の和は fiber の単位。
方針：shift を外し cone の二射影の分解恒等式へ戻す。
規約：全 Hom end の実単位を使う。使われ方：β3 の双対比較の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 逆射の第一成分と収縮成分は fiber の実単位を分解する。 -/
lemma dgModuleFiberCofiberSectionFirst_decomposition (f : M ⟶ N) :
    compose A (dgModuleFiberCofiberSectionFirst A D f) (dgModuleFiberNullHomotopy A D f)
        (show (-1) + 1 = 0 by decide) +
      compose A (dgModuleFiberCofiberContractionT A D f) (dgModuleFiberProjectionElement A D f)
        (zero_add 0) = (unitElement A (dgModuleFiber A D f)).val := by
  let out : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1) := moduleShiftOutElement A D (-1)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))
  have ha : compose A out (dgModuleFiberCofiberSectionFirst A D f)
      (show 1 + (-1) = 0 by decide) = -moduleConeInrElement A D f :=
    dgModuleFiberCofiberSectionFirst_unshift A D f
  have ht : compose A out (dgModuleFiberCofiberContractionT A D f) (zero_add (-1)) =
      moduleConeInlElement A D f :=
    (dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1)).apply_symm_apply _
  have h1 := compose_assoc_of_sum (A := A) (dgModuleFiberNullHomotopy A D f)
    (dgModuleFiberCofiberSectionFirst A D f) out (show (-1) + 1 = 0 by decide)
    (show 1 + (-1) = 0 by decide) (show (-1) + 1 + (-1) = -1 by decide)
  have h2 := compose_assoc_of_sum (A := A) (dgModuleFiberProjectionElement A D f)
    (dgModuleFiberCofiberContractionT A D f) out (zero_add 0) (zero_add (-1)) (zero_add (-1))
  apply (dgModuleNegativeShiftTargetHomEquiv A D (dgModuleFiber A D f)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1)).injective
  rw [map_add]
  change compose A out _ (zero_add (-1)) + compose A out _ (zero_add (-1)) =
    compose A out (unitElement A (dgModuleFiber A D f)).val (zero_add (-1))
  rw [h1, h2, ha, ht, compose_unit, dgModuleCompose_neg_left,
    dgModuleFiberNullHomotopy, dgModuleFiberProjectionElement,
    dgModuleCompose_neg_right, neg_neg]
  have hc1 := compose_assoc_of_sum (A := A) out (moduleConeSndElement A D f)
    (moduleConeInrElement A D f) (add_zero (-1)) (add_zero 0) (add_zero (-1))
  have hc2 := compose_assoc_of_sum (A := A) out (moduleConeFstElement A D f)
    (moduleConeInlElement A D f) (show (-1) + 1 = 0 by decide) (add_neg_cancel 1)
    (show (-1) + 1 + (-1) = -1 by decide)
  have hc : compose A (moduleConeInrElement A D f) (moduleConeSndElement A D f) (add_zero 0) +
      compose A (moduleConeInlElement A D f) (moduleConeFstElement A D f) (add_neg_cancel 1) =
      (unitElement A (ForgetEnrichment.to (Complex A) (moduleCone A D f))).val :=
    (add_comm _ _).trans (moduleCone_decomposition A D f)
  rw [hc1, hc2, ← compose_add_left, hc, unit_compose]

end SerrePositivity.InfinityCategories
