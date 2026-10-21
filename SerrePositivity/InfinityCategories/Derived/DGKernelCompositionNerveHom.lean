module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveValue
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawTransport
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerveAlgebra
/-!
概要：通常 kernel の指定合成比較の射を、同じ双加群逆結合子の nerve 像へ戻す。
方針：同じ dg 関手の端点等式と、指定同型の異種等式を保つ。
規約：任意の頂点成分一致で代用しない。使われ方：通常 kernel の pentagon。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
/-- 元の通常合成比較の射は、同じ逆結合子の全関手射の像を保つ。 -/
lemma dgKernelTensorCompositionNerveIso_hom_heq
    (P : Bimodule R E D) (Q : Bimodule R F E) :
    HEq (dgKernelTensorCompositionNerveIso R D E F P Q).hom
      ((dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
        (BimoduleTensor.associatorIso R F E D (RightModule R D) Q P
          (DGFunctor.id (RightModule R D))).inv) := by
  have hf : dgNerve.map (Morita.kernelTensor R D E P) ≫
      dgNerve.map (Morita.kernelTensor R E F Q) =
      dgNerve.map (BimoduleTensor.compose R F E (RightModule R D) Q
        (BimoduleTensor.compose R E D (RightModule R D) P
          (DGFunctor.id (RightModule R D)))).toFunctor := by
    rw [← dgNerve.map_comp, Morita.kernelTensorComposition_eq]
  have hh := functorIso_hom_heq (dgKernelTensorCompositionNerveIso R D E F P Q)
    (dgBimoduleIsoNerve R F (RightModule R D)
      (BimoduleTensor.associatorIso R F E D (RightModule R D) Q P
        (DGFunctor.id (RightModule R D))).symm) hf rfl
    (dgKernelTensorCompositionNerveIso_heq R D E F P Q)
  rw [← dgBimoduleFunctorHomFunctor_mapIso] at hh
  exact hh
end
end SerrePositivity.InfinityCategories
