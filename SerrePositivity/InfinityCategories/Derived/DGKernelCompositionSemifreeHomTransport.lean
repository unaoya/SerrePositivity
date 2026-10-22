module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorCompositionSemifreeTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoWhiskerHomTransport
/-!
概要：元の通常 tensor 比較の半自由制限と共通出力分解後の射を回収する。
方針：端点の等式・同じ同型の値・実前後合成を不透明な補題で接続する。
規約：比較の指定値・計算上限を変更しない。使われ方：κ の右変数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
lemma dgKernelTensorCompositionSemifreeIso_source_eq
    (P : Bimodule R E D) (Q : Bimodule R K E) :
    dgNerve.map ((dgSemifreeKernelModuleDG R D E P).comp
      (Morita.kernelTensor R E K Q)) =
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)) ≫
        (dgNerve.map (Morita.kernelTensor R D E P) ≫
          dgNerve.map (Morita.kernelTensor R E K Q)) := by
  simp only [dgSemifreeKernelModuleDG, dgNerve.map_comp, Category.assoc]
lemma dgKernelTensorCompositionSemifreeIso_target_eq
    (P : Bimodule R E D) (Q : Bimodule R K E) :
    dgNerve.map (dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P)) =
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)) ≫
        dgNerve.map (Morita.kernelTensor R D K (BimoduleTensor.compose R K E D Q P)) := by
  simp only [dgSemifreeKernelModuleDG, dgNerve.map_comp]
lemma dgKernelTensorCompositionSemifreeIso_hom_precomp_heq
    (P : Bimodule R E D) (Q : Bimodule R K E) :
    HEq (dgKernelTensorCompositionSemifreeIso R D E K P Q).hom
      ((dgKernelTensorCompositionNerveIso R D E K P Q).precomp
        (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)))).hom := by
  exact functorIso_hom_heq_of_endpoint_heq
    (dgKernelTensorCompositionSemifreeIso R D E K P Q)
    ((dgKernelTensorCompositionNerveIso R D E K P Q).precomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D))))
    (dgKernelTensorCompositionSemifreeIso_source_eq R D E K P Q)
    (dgKernelTensorCompositionSemifreeIso_target_eq R D E K P Q)
    (dgKernelTensorCompositionSemifreeIso_heq R D E K P Q)
lemma dgKernelTensorCompositionSemifreeIso_hom_heq
    (P : Bimodule R E D) (Q : Bimodule R K E) :
    HEq (dgKernelTensorCompositionSemifreeIso R D E K P Q).hom
      (functorHomPrecomp
        (dgNerve.map (Morita.kernelTensor R D E P) ≫
          dgNerve.map (Morita.kernelTensor R E K Q))
        (dgNerve.map (Morita.kernelTensor R D K (BimoduleTensor.compose R K E D Q P)))
        (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)))
        (dgKernelTensorCompositionNerveIso R D E K P Q).hom) := by
  exact (dgKernelTensorCompositionSemifreeIso_hom_precomp_heq R D E K P Q).trans
    (heq_of_eq (functorIso_precomp_hom_typed
      (dgKernelTensorCompositionNerveIso R D E K P Q)
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)))))
lemma dgKernelTensorCompositionSemifreeIso_postcomp_hom_heq
    (P : Bimodule R E D) (Q : Bimodule R K E) :
    HEq ((dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (dgModuleResolvedInfinity R (RightModule R K) K
          (DGFunctor.id (RightModule R K)))).hom
      (functorHomPostcomp
        (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)) ≫
          (dgNerve.map (Morita.kernelTensor R D E P) ≫
            dgNerve.map (Morita.kernelTensor R E K Q)))
        (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)) ≫
          dgNerve.map (Morita.kernelTensor R D K (BimoduleTensor.compose R K E D Q P)))
        (dgModuleResolvedInfinity R (RightModule R K) K
          (DGFunctor.id (RightModule R K)))
        (functorHomPrecomp
          (dgNerve.map (Morita.kernelTensor R D E P) ≫
            dgNerve.map (Morita.kernelTensor R E K Q))
          (dgNerve.map (Morita.kernelTensor R D K (BimoduleTensor.compose R K E D Q P)))
          (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
            (dgModuleSemifreeProperty R D)))
          (dgKernelTensorCompositionNerveIso R D E K P Q).hom)) := by
  exact functorIso_precomp_postcomp_hom_transport
    (dgKernelTensorCompositionSemifreeIso R D E K P Q)
    (dgKernelTensorCompositionNerveIso R D E K P Q)
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleSemifreeProperty R D)))
    (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
    (dgKernelTensorCompositionSemifreeIso_source_eq R D E K P Q)
    (dgKernelTensorCompositionSemifreeIso_target_eq R D E K P Q)
    (dgKernelTensorCompositionSemifreeIso_heq R D E K P Q)
end SerrePositivity.InfinityCategories
