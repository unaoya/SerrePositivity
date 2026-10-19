module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberRetraction

/-! # 標準 cofiber の fiber 比較の収縮の行列式

概要：第二 cone 射影と fiber の零ホモトピーの合成の微分と分解式を求める。
方針：Leibniz 則と全 Hom end の cone の行列恒等式を使う。
規約：実際の次数 −1 成分。使われ方：β3 の比較のもう一方の合成の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 比較の収縮に使う N への次数 −1 成分。 -/
def dgModuleCofiberFiberContractionN (f : M ⟶ N) :
    GradedHom A (dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (Complex A) N) (-1) :=
  compose A (moduleConeSndElement A D f)
    (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (add_zero (-1))

/-- 収縮の第一成分の微分は射影と元の射による差。 -/
lemma dgModuleCofiberFiberContractionN_differential (f : M ⟶ N) :
    (moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (Complex A) N)).d (-1) 0
        (dgModuleCofiberFiberContractionN A D f) =
      -compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
        (dgModuleCofiberFiberRetractElement A D f) (zero_add 0) +
      dgModuleFiberProjectionElement A D (moduleConeInr A D f) := by
  have hn : differential (D := RightModule A D) A
      (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) =
      compose A (moduleConeInrElement A D f)
        (dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (zero_add 0) := by
    have h := dgModuleFiberNullHomotopy_differential A D (moduleConeInr A D f)
    rw [dgModuleClosedCycle_comp, dgModuleFiberProjection_cycle] at h
    exact h
  have hs : differential (D := RightModule A D) A (moduleConeSndElement A D f) =
      -compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
        (moduleConeFstElement A D f) (add_zero 1) := dgModuleConeSndElement_d A D f
  have hfirst := compose_assoc_of_sum (A := A)
    (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeFstElement A D f)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
    (show (-1) + 1 = 0 by decide) (add_zero 1) (show (-1) + 1 + 0 = 0 by decide)
  have hlast := compose_assoc_of_sum (A := A)
    (dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (moduleConeInrElement A D f)
    (moduleConeSndElement A D f) (zero_add 0) (zero_add 0) (zero_add 0)
  rw [moduleCone_inr_snd, unit_compose] at hlast
  change differential A (dgModuleCofiberFiberContractionN A D f) = _
  rw [dgModuleCofiberFiberContractionN, differential_compose, hs, hn,
    dgModuleCompose_neg_left, ← hfirst, hlast]
  simp only [Int.negOnePow_zero, one_smul]
  rfl

/-- cone の二射影による分解を fiber の零ホモトピーへ適用した恒等式。 -/
lemma dgModuleCofiberFiberContractionN_decomposition (f : M ⟶ N) :
    compose A (moduleConeInlElement A D f) (dgModuleCofiberFiberRetractElement A D f)
        (zero_add (-1)) +
      compose A (moduleConeInrElement A D f) (dgModuleCofiberFiberContractionN A D f)
        (add_zero (-1)) = dgModuleFiberNullHomotopy A D (moduleConeInr A D f) := by
  have hfirst := compose_assoc_of_sum (A := A)
    (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeFstElement A D f)
    (moduleConeInlElement A D f) (show (-1) + 1 = 0 by decide) (add_neg_cancel 1)
    (show (-1) + 1 + (-1) = -1 by decide)
  have hlast := compose_assoc_of_sum (A := A)
    (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeSndElement A D f)
    (moduleConeInrElement A D f) (add_zero (-1)) (add_zero 0) (add_zero (-1))
  change compose A (moduleConeInlElement A D f)
      (compose A (moduleConeFstElement A D f)
        (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (by decide)) (zero_add (-1)) +
    compose A (moduleConeInrElement A D f)
      (compose A (moduleConeSndElement A D f)
        (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (add_zero (-1)))
      (add_zero (-1)) = _
  rw [hfirst, hlast, ← compose_add_left, moduleCone_decomposition, unit_compose]

end SerrePositivity.InfinityCategories
