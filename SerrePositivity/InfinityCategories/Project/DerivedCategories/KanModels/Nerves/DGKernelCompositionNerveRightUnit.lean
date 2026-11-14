module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGKernelIdentityNerveHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGKernelCompositionNerveWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGKernelBimoduleIsoNerveHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomTwoThreeTransport
public import SerrePositivity.DifferentialGraded.Tensor.Graded
/-!
概要：元の通常 kernel 合成比較の右単位三角式を証明する。
方針：元の指定値と端点等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：kernel の単位・結合 coherence。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
private lemma inv_comp_of_eq {C : Type*} [Category C] {X Y Z : C}
    (a : X ≅ Y) (b : X ⟶ Z) (c : Y ⟶ Z) (h : b = a.hom ≫ c) : a.inv ≫ b = c := by
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
variable (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の dg 単位三角の反転経路を、同じ全関手射の実像へ送る。 -/
lemma dgBimoduleNerve_inverse_unit_triangle (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R E D D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E D P).hom
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))))) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P))
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).hom) := by
  have h := inv_comp_of_eq
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R E D D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))) _ _
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.triangle R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)).map m) h
/-- 元の通常単位の後合成は、同じ composeMap の実像を保つ。 -/
lemma dgKernelIdentityNerveIso_postcomp_hom_heq (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P))
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
            (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).hom)) := by
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso_hom_heq R D
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D) _ rfl
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id.symm ha (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_nerve_hom_heq R D E (RightModule R D)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).hom (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P)
  exact hh.trans hm.symm
/-- 元の通常合成比較と右単位子の作用は、元の単位の後合成と一致する。 -/
lemma dgKernelTensorCompositionNerveIso_right_unit (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso R D D E (Bimodule.diagonal R D) P ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E D P) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P)) := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D D (Bimodule.diagonal R D)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleTensor.compose R E D (RightModule R D) P
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R D D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))).toFunctor := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Morita.kernelTensorComposition_eq]
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorCompositionNerveIso_hom_heq R D D E (Bimodule.diagonal R D) P
  have hr := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso_hom R D E
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E D P))
  have hu := dgKernelIdentityNerveIso_postcomp_hom_heq R D E P
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq _ _ _ _ hf rfl rfl hc hr
  have he := dgBimoduleNerve_inverse_unit_triangle R D E P
  apply Iso.ext
  exact eq_of_heq (hL.trans ((heq_of_eq he).trans hu.symm))
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
