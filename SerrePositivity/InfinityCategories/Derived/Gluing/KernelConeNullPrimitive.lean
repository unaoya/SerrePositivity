module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelLeftInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeNullElementKernel
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCochainPrimitive

/-! 指定した標準 kernel 円錐の零ホモトピーは、第三成分が零。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "μ" => dgGluingDifference R C D M Y Y
local notation "h" => dgGluingKernelConeNullCochain R C D M Y Z f
local notation "d" => dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F KY L

/-- 同じ指定 kernel cochain の第三成分は、単位の比較成分が零であるため零。 -/
lemma dgGluingKernelConeNullCochain_primitive :
    (h).comp (mappingCocone.snd d) (by omega : -1 + -1 = -2) = 0 := by
  have hi := dgGluingIdentity_comparison R C D M Y
  change (Cochain.ofHom (dgGluingIdentity R C D M Y)).comp
    (mappingCocone.snd μ) (zero_add (-1)) = 0 at hi
  have he := congrArg
    (fun z => (Cochain.ofHom (dgGluingIdentity R C D M Y)).comp z (zero_add (-2)))
    (dgGluingHomConeKernelIso_inl_snd R C D M Y Y Z f)
  simp only [Cochain.comp_neg, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    hi, Cochain.zero_comp, neg_zero] at he
  simpa only [dgGluingKernelConeNullCochain,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_second_is_zero_cochain] using he

/-- 単位の 1 で評価した指定次数 −1 元も、同じ第三成分が零。 -/
lemma dgGluingKernelConeNullElement_primitive :
    (mappingCocone.snd d).v (-1) (-2) (by omega)
      (dgGluingKernelConeNullElement R C D M Y Z f) = 0 :=
  dgGluingUnitCochainElement_comp_zero (h) (mappingCocone.snd d)
    (dgGluingKernelConeNullCochain_primitive R C D M Y Z f)

end SerrePositivity.InfinityCategories
