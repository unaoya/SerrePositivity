module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleMapPrecomp
/-!
概要：元の kernel 射の実全関手射とその前後合成を、同じ composeMap の像へ戻す。
方針：実厳密変換と全 nerve 変換の同じ入力・出力作用を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：指定合成子 α の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
/-- 元の通常 kernel 射の全関手射は、同じ composeMap の実像。 -/
lemma dgKernelTensorFunctorHomFunctor_map {P P' : BimoduleCategory R E D} (f : P ⟶ P') :
    (dgKernelTensorFunctorHomFunctor R D E).map f =
      (dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
        (BimoduleTensor.composeMap R E D (RightModule R D) f
          (𝟙 (BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D))))) := rfl
/-- 元の kernel 射の通常後合成は、同じ composeMap の全関手射。 -/
lemma dgKernelTensorFunctorHomFunctor_postcomp_heq {P P' : BimoduleCategory R E D}
    (f : P ⟶ P') (Q : Bimodule R F E) :
    HEq ((SSet.mapHomotopyCategory ((ihom (dgModuleNerve R D)).map
      (dgNerve.map (Morita.kernelTensor R E F Q)))).map
        ((dgKernelTensorFunctorHomFunctor R D E).map f))
      ((dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
        (BimoduleTensor.composeMap R F E (RightModule R D)
          (𝟙 (BimoduleCategory.of R F E Q))
          (BimoduleTensor.composeMap R E D (RightModule R D) f
            (𝟙 (BimoduleCategory.of R D (RightModule R D)
              (DGFunctor.id (RightModule R D))))))) := by
  exact (dgKernelTensor_postcomp_nerve_hom_heq R E F (RightModule R D)
    (BimoduleTensor.composeMap R E D (RightModule R D) f
      (𝟙 (BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D)))))
    (BimoduleCategory.of R F E Q)).symm
/-- 元の kernel 射の通常前合成は、同じ composeMap の全関手射。 -/
lemma dgKernelTensorFunctorHomFunctor_precomp_heq {Q Q' : BimoduleCategory R F E}
    (g : Q ⟶ Q') (P : Bimodule R E D) :
    HEq ((SSet.mapHomotopyCategory ((pre (dgNerve.map (Morita.kernelTensor R D E P))).app
      (dgModuleNerve R F))).map ((dgKernelTensorFunctorHomFunctor R E F).map g))
      ((dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
        (BimoduleTensor.composeMap R F E (RightModule R D) g
          (𝟙 (BimoduleCategory.of R E (RightModule R D) (Morita.kernelTensor R D E P))))) := by
  exact (dgKernelBimoduleMap_precomp_nerve_hom_heq R E F (RightModule R D) g
    (Morita.kernelTensor R D E P)).symm
end
end SerrePositivity.InfinityCategories
