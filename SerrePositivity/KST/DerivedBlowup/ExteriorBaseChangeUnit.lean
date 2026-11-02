module

public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainBaseChangeInclusion
public import SerrePositivity.KST.DerivedBlowup.ExteriorDGCategory
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules

/-!
概要：KST Def3.1 の Koszul cochain 底変更同型は単位を保つ。
方針：単位からの射を次数0の1で評価し、逆代数底変更写像の1保存を使う。
規約：既存の強モノイダルな係数変更の unitIso を用いる。
使われ方：底変更 dg 関手の map_id。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：単位複体の係数変更同型の逆は1を1⊗1へ送る。
方針：順単位比較の1での公式と逆元律を使う。
規約：KST Def3.1。使われ方：Koszul 単位射の係数変更。 -/
theorem exteriorScalarUnitIso_inv_one (φ : R →+* S) :
    letI := φ.toAlgebra
    (DifferentialGraded.ScalarExtension.unitIso φ).inv.f 0 (1 : S) = (1 : S) ⊗ₜ[R] (1 : R) := by
  let := φ.toAlgebra
  apply (ModuleCat.mono_iff_injective
    ((DifferentialGraded.ScalarExtension.unitIso φ).hom.f 0)).mp inferInstance
  have hs := DifferentialGraded.ScalarExtension.sphereIso_one φ 0
  change (DifferentialGraded.ScalarExtension.unitIso φ).hom.f 0
    ((1 : S) ⊗ₜ[R] (1 : R)) = (1 : S) at hs
  have hi := congrArg (fun f => f.f 0) (DifferentialGraded.ScalarExtension.unitIso φ).inv_hom_id
  exact (congr($(hi).hom (1 : S))).trans hs.symm

/-- 概要：逆 Koszul cochain 底変更同型は強モノイダル係数変更の単位を保つ。
方針：次数0の1で評価し、総外積への単射で逆代数底変更の1保存を比較する。
規約：KST Def3.1。使われ方：底変更 dg 関手の map_id。 -/
theorem exteriorCochainBaseChange_unit (φ : R →+* S) (d : M →ₗ[R] R) :
    letI := φ.toAlgebra
    (DifferentialGraded.ScalarExtension.unitIso φ).inv ≫
        (DifferentialGraded.ScalarExtension.extension φ).map (exteriorKoszulUnit d) ≫
          (exteriorCochainBaseChangeIso φ d).inv =
      exteriorKoszulUnit (exteriorBaseChangeDifferential (S := S) d) := by
  let := φ.toAlgebra
  apply (DifferentialGraded.unitCycleEquiv
    (exteriorKoszulCochain (exteriorBaseChangeDifferential (S := S) d))).injective
  apply Subtype.ext
  change (exteriorCochainBaseChangeIso φ d).inv.f 0
      ((ModuleCat.extendScalars φ).map ((exteriorKoszulUnit d).f 0)
        ((DifferentialGraded.ScalarExtension.unitIso φ).inv.f 0 (1 : S))) =
    (exteriorKoszulUnit (exteriorBaseChangeDifferential (S := S) d)).f 0 (1 : S)
  rw [exteriorScalarUnitIso_inv_one]
  erw [ModuleCat.ExtendScalars.map_tmul φ]
  apply exteriorCochainInclusion_injective (exteriorBaseChangeDifferential (S := S) d) 0
  rw [exteriorBaseChangeCochainInclusion_iso_inv, exteriorKoszulUnit_inclusion,
    map_one (algebraMap S (ExteriorAlgebra S (S ⊗[R] M)))]
  change exteriorOfBaseChange ((1 : S) ⊗ₜ[R]
    exteriorCochainInclusion d 0 ((exteriorKoszulUnit d).f 0 (1 : R))) = 1
  rw [exteriorKoszulUnit_inclusion, map_one (algebraMap R (ExteriorAlgebra R M))]
  exact map_one exteriorOfBaseChange

end SerrePositivity.KST.DerivedBlowup
