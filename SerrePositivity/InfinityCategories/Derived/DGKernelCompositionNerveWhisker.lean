module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveHom
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleAssociatorPrecomp
public import SerrePositivity.InfinityCategories.Derived.DGKernelCoherencePathTools
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerHEq
/-!
概要：元の通常 kernel 合成比較の前後合成を、同じ双加群五角の二辺へ同定する。
方針：元の全関手射・厳密変換・全円柱を保って、端点等式を輸送する。
規約：指定比較を変更しない。使われ方：通常 kernel の五角経路全体の等式。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F] [DGCategory R G] [Small.{u} G]
private lemma source_eq (P : Bimodule R E D) (Q : Bimodule R F E) :
    dgNerve.map (Morita.kernelTensor R D E P) ≫ dgNerve.map (Morita.kernelTensor R E F Q) =
    dgNerve.map (BimoduleTensor.compose R F E (RightModule R D) Q
      (BimoduleTensor.compose R E D (RightModule R D) P
        (DGFunctor.id (RightModule R D)))).toFunctor := by
  rw [← dgNerve.map_comp, Morita.kernelTensorComposition_eq]
/-- 元の通常合成比較の後合成は、同じ composeMap の実像を保つ。 -/
lemma dgKernelAlpha_postcomp_hom_heq
    (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F) :
    HEq ((dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
      (dgNerve.map (Morita.kernelTensor R F G S))).hom
      ((dgBimoduleFunctorHomFunctor R G (RightModule R D)).map
        (BimoduleTensor.composeMap R G F (RightModule R D)
          (𝟙 (BimoduleCategory.of R G F S))
          (BimoduleTensor.associatorIso R F E D (RightModule R D) Q P
            (DGFunctor.id (RightModule R D))).inv)) := by
  have ha := dgKernelTensorCompositionNerveIso_hom_heq R D E F P Q
  have hh := functorIso_postcomp_hom_heq
    (dgKernelTensorCompositionNerveIso R D E F P Q) _ (source_eq R D E F P Q) rfl ha
    (dgNerve.map (Morita.kernelTensor R F G S))
  have hm := dgKernelTensor_postcomp_nerve_hom_heq R F G (RightModule R D)
    (BimoduleTensor.associatorIso R F E D (RightModule R D) Q P
      (DGFunctor.id (RightModule R D))).inv (BimoduleCategory.of R G F S)
  exact hh.trans hm.symm
/-- 元の通常合成比較の前合成は、同じ逆結合子の実像を保つ。 -/
lemma dgKernelAlpha_precomp_hom_heq
    (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F) :
    HEq ((dgKernelTensorCompositionNerveIso R E F G Q S).precomp
      (dgNerve.map (Morita.kernelTensor R D E P))).hom
      ((dgBimoduleFunctorHomFunctor R G (RightModule R D)).map
        (BimoduleTensor.associatorIso R G F E (RightModule R D) S Q
          (BimoduleTensor.compose R E D (RightModule R D) P
            (DGFunctor.id (RightModule R D)))).inv) := by
  have ha := dgKernelTensorCompositionNerveIso_hom_heq R E F G Q S
  have hh := functorIso_precomp_hom_heq
    (dgKernelTensorCompositionNerveIso R E F G Q S) _ (source_eq R E F G Q S) rfl ha
    (dgNerve.map (Morita.kernelTensor R D E P))
  have hm := dgBimoduleAssociator_precomp_nerve_inv_heq R E F
    (RightModule R E) (RightModule R D) G (Morita.kernelTensor R D E P) S Q
    (DGFunctor.id (RightModule R E))
  rw [dgFunctor_comp_identity] at hm
  exact hh.trans hm.symm
end
end SerrePositivity.InfinityCategories
