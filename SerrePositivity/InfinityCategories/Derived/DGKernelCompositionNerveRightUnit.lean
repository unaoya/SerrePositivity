module
public import SerrePositivity.InfinityCategories.Derived.DGKernelIdentityNerveHom
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveWhisker
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleIsoNerveHom
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTwoThreeTransport
public import SerrePositivity.DifferentialGraded.Tensor.Triangle
/-!
概要：元の通常 kernel 合成比較の右単位三角式を証明する。
方針：元の指定値と端点等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：kernel の単位・結合 coherence。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma inv_comp_of_eq {C : Type*} [Category C] {X Y Z : C}
    (a : X ≅ Y) (b : X ⟶ Z) (c : Y ⟶ Z) (h : b = a.hom ≫ c) : a.inv ≫ b = c := by
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
variable (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 元の dg 単位三角の反転経路を、同じ全関手射の実像へ送る。 -/
lemma dgBimoduleNerve_inverse_unit_triangle (P : Bimodule R E D) :
    (dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
      (BimoduleTensor.associatorIso R E D D (RightModule R D) P
        (Bimodule.diagonal R D) (DGFunctor.id (RightModule R D))).inv ≫
    (dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
      (BimoduleTensor.composeMap R E D (RightModule R D)
        (BimoduleTensor.rightBimoduleUnitIso R E D P).hom
        (𝟙 (BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D))))) =
    (dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
      (BimoduleTensor.composeMap R E D (RightModule R D)
        (𝟙 (BimoduleCategory.of R E D P))
        (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D)
          (DGFunctor.id (RightModule R D))).hom) := by
  have h := inv_comp_of_eq
    (BimoduleTensor.associatorIso R E D D (RightModule R D) P
      (Bimodule.diagonal R D) (DGFunctor.id (RightModule R D))) _ _
    (BimoduleTensor.triangle R E D (RightModule R D) P
      (DGFunctor.id (RightModule R D)))
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (dgBimoduleFunctorHomFunctor R E (RightModule R D)).map m) h
/-- 元の通常単位の後合成は、同じ composeMap の実像を保つ。 -/
lemma dgKernelIdentityNerveIso_postcomp_hom_heq (P : Bimodule R E D) :
    HEq ((dgKernelIdentityNerveIso R D).postcomp
      (dgNerve.map (Morita.kernelTensor R D E P))).hom
      ((dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
        (BimoduleTensor.composeMap R E D (RightModule R D)
          (𝟙 (BimoduleCategory.of R E D P))
          (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D)
            (DGFunctor.id (RightModule R D))).hom)) := by
  have ha := dgKernelIdentityNerveIso_hom_heq R D
  have hh := functorIso_postcomp_hom_heq (dgKernelIdentityNerveIso R D) _ rfl
    dgNerve.map_id.symm ha (dgNerve.map (Morita.kernelTensor R D E P))
  have hm := dgKernelTensor_postcomp_nerve_hom_heq R D E (RightModule R D)
    (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D)
      (DGFunctor.id (RightModule R D))).hom (BimoduleCategory.of R E D P)
  exact hh.trans hm.symm
/-- 元の通常合成比較と右単位子の作用は、元の単位の後合成と一致する。 -/
lemma dgKernelTensorCompositionNerveIso_right_unit (P : Bimodule R E D) :
    dgKernelTensorCompositionNerveIso R D D E (Bimodule.diagonal R D) P ≪≫
      dgKernelTensorIsoNerveOfBimoduleIso R D E
        (BimoduleTensor.rightBimoduleUnitIso R E D P) =
    (dgKernelIdentityNerveIso R D).postcomp (dgNerve.map (Morita.kernelTensor R D E P)) := by
  have hf : dgNerve.map (Morita.kernelTensor R D D (Bimodule.diagonal R D)) ≫
      dgNerve.map (Morita.kernelTensor R D E P) =
      dgNerve.map (BimoduleTensor.compose R E D (RightModule R D) P
        (BimoduleTensor.compose R D D (RightModule R D) (Bimodule.diagonal R D)
          (DGFunctor.id (RightModule R D)))).toFunctor := by
    rw [← dgNerve.map_comp, Morita.kernelTensorComposition_eq]
  have hc := dgKernelTensorCompositionNerveIso_hom_heq R D D E (Bimodule.diagonal R D) P
  have hr := heq_of_eq (dgKernelTensorIsoNerveOfBimoduleIso_hom R D E
    (BimoduleTensor.rightBimoduleUnitIso R E D P))
  have hu := dgKernelIdentityNerveIso_postcomp_hom_heq R D E P
  have hL := functorHom_comp_heq _ _ _ _ hf rfl rfl hc hr
  have he := dgBimoduleNerve_inverse_unit_triangle R D E P
  apply Iso.ext
  exact eq_of_heq (hL.trans ((heq_of_eq he).trans hu.symm))
end
end SerrePositivity.InfinityCategories
