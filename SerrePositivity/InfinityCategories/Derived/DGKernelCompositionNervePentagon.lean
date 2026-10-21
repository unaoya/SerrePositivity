module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveWhisker
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleNerveInversePentagon
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleIsoNerveHom
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTwoThreeTransport
/-!
概要：元の通常 kernel 合成比較の三 kernel 五角経路を、全関手同型として証明する。
方針：同じ双加群逆五角の実像の各辺を、元の指定比較へ端点付きで同定する。
規約：頂点成分一致へ弱めず、原 Hom の平坦性を仮定しない。
使われ方：K-flat の通常比較と元の導来合成子への coherence の移送。
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
/-- 元の通常 kernel の指定合成比較は、同じ双加群結合子と五角経路を満たす。 -/
lemma dgKernelTensorCompositionNerveIso_pentagon
    (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F) :
    (dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
        (dgNerve.map (Morita.kernelTensor R F G S)) ≪≫
      dgKernelTensorCompositionNerveIso R D F G (BimoduleTensor.compose R F E D Q P) S =
    (dgKernelTensorCompositionNerveIso R E F G Q S).precomp
        (dgNerve.map (Morita.kernelTensor R D E P)) ≪≫
      dgKernelTensorCompositionNerveIso R D E G P (BimoduleTensor.compose R G F E S Q) ≪≫
      dgKernelTensorIsoNerveOfBimoduleIso R D G
        (BimoduleTensor.associatorIso R G F E D S Q P) := by
  have hf : (dgNerve.map (Morita.kernelTensor R D E P) ≫
      dgNerve.map (Morita.kernelTensor R E F Q)) ≫
      dgNerve.map (Morita.kernelTensor R F G S) =
      dgNerve.map (BimoduleTensor.compose R G F (RightModule R D) S
        (BimoduleTensor.compose R F E (RightModule R D) Q
          (BimoduleTensor.compose R E D (RightModule R D) P
            (DGFunctor.id (RightModule R D))))).toFunctor := by
    rw [source_eq R D E F P Q, ← dgNerve.map_comp, dgKernelTensor_postcomp_bimodule_eq]
  have hg := source_eq R D F G (BimoduleTensor.compose R F E D Q P) S
  have hh := source_eq R D E G P (BimoduleTensor.compose R G F E S Q)
  apply Iso.ext
  change ((dgKernelTensorCompositionNerveIso R D E F P Q).postcomp
      (dgNerve.map (Morita.kernelTensor R F G S))).hom ≫
    (dgKernelTensorCompositionNerveIso R D F G (BimoduleTensor.compose R F E D Q P) S).hom =
    ((dgKernelTensorCompositionNerveIso R E F G Q S).precomp
      (dgNerve.map (Morita.kernelTensor R D E P))).hom ≫
    (dgKernelTensorCompositionNerveIso R D E G P (BimoduleTensor.compose R G F E S Q)).hom ≫
    (dgKernelTensorIsoNerveOfBimoduleIso R D G
      (BimoduleTensor.associatorIso R G F E D S Q P)).hom
  exact functorHom_two_three_eq_of_heq _ _ _ _ _ _ _ _ _ _ hf hg hh rfl rfl
    (dgKernelAlpha_postcomp_hom_heq R D E F G P Q S)
    (dgKernelTensorCompositionNerveIso_hom_heq R D F G
      (BimoduleTensor.compose R F E D Q P) S)
    (dgKernelAlpha_precomp_hom_heq R D E F G P Q S)
    (dgKernelTensorCompositionNerveIso_hom_heq R D E G P
      (BimoduleTensor.compose R G F E S Q))
    (heq_of_eq (dgKernelTensorIsoNerveOfBimoduleIso_hom R D G
      (BimoduleTensor.associatorIso R G F E D S Q P)))
    (dgBimoduleNerve_inverse_pentagon_hom R G F E D (RightModule R D) S Q P
      (DGFunctor.id (RightModule R D)))
end
end SerrePositivity.InfinityCategories
