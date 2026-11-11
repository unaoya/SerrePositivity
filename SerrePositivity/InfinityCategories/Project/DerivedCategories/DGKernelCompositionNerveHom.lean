module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositionNerveValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleIsoNerveAlgebra
/-!
概要：通常 kernel の指定合成比較の射を、同じ双加群逆結合子の nerve 像へ戻す。
方針：同じ dg 関手の端点等式と、指定同型の異種等式を保つ。
規約：任意の頂点成分一致で代用しない。使われ方：通常 kernel の pentagon。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
/-- 元の通常合成比較の射は、同じ逆結合子の全関手射の像を保つ。 -/
lemma dgKernelTensorCompositionNerveIso_hom_heq
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R F E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q P
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).inv) := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F Q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleTensor.compose R F E (RightModule R D) Q
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))).toFunctor := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Morita.kernelTensorComposition_eq]
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D E F P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleIsoNerve R F (RightModule R D)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R F E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q P
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).symm) hf rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_heq R D E F P Q)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor_mapIso] at hh
  exact hh
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
