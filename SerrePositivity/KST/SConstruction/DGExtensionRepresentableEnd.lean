module
public import SerrePositivity.KST.SConstruction.DGEndIsoNaturality
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGGraphCompositionInputLeft
public import SerrePositivity.KST.SConstruction.DGPerfectEndIsoComparison
public import SerrePositivity.KST.SConstruction.DGRepresentableThickGeneration

/-! # 元の代表加群の延長 End と元の dg 射の回収
概要：同じ代表延長同型による End 共役と Yoneda 逆写像で、元の dg 射を回収する。
方針：既存の全次数自然性を、同じ閉同型に対する共役の回収式へ渡す。
規約：同じ実延長・元の全 Hom を保持。使われ方：⊙ 比較の元の右代数射との可換性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E) (b : D)

/-- 同じ代表延長の全 End 作用を共役すると、元の F の代表加群上の作用に一致する。 -/
lemma dgExtensionRepresentableEnd_conjugate :
    (yonedaHom R D b b ≫ (dgModuleExtension R D E F).map
      (representable R b) (representable R b)) ≫
        dgEndIsoHom R (D := RightModule R E) (dgModuleExtensionRepresentableIso R D E F b) =
      F.map b b ≫ yonedaHom R E (F.obj b) (F.obj b) := by
  apply dgEndIsoHom_of_naturality R (D := RightModule R E)
    (dgModuleExtensionRepresentableIso R D E F b)
  have h := dgModuleExtensionRepresentableIso_naturality R D E F b b
  change yonedaHom R D b b ≫ (dgModuleExtension R D E F).map
      (representable R b) (representable R b) ≫
        eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R)
            ((dgModuleExtension R D E F).obj (representable R b)))
          (dgModuleExtensionRepresentableIso R D E F b).hom =
    F.map b b ≫ yonedaHom R E (F.obj b) (F.obj b) ≫
      eHomWhiskerRight (Complex R) (dgModuleExtensionRepresentableIso R D E F b).hom
        (ForgetEnrichment.of (Complex R) (representable R (F.obj b))) at h
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

/-- 同じ代表延長の End を元の Yoneda 逆 Hom で戻せば、元の F の全 Hom を回収する。 -/
lemma dgExtensionRepresentableEnd_inverseYoneda :
    ((yonedaHom R D b b ≫ (dgModuleExtension R D E F).map
      (representable R b) (representable R b)) ≫
        dgEndIsoHom R (D := RightModule R E) (dgModuleExtensionRepresentableIso R D E F b)) ≫
          (dgYonedaIso R (F.obj b) (representable R (F.obj b))).hom = F.map b b := by
  rw [dgExtensionRepresentableEnd_conjugate]
  erw [Category.assoc]
  exact (congrArg (fun f => F.map b b ≫ f)
    (dgYonedaIso R (F.obj b) (representable R (F.obj b))).inv_hom_id).trans
      (Category.comp_id _)

end SerrePositivity.KST.SConstruction
