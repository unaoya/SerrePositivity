module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGBimoduleInverseAssociatorNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGKernelTensorIsoNerveAlgebra
/-!
概要：通常 kernel の逆結合子の自然性を、同じ二つの変数の作用へ分解する。
方針：元の composeMap の合成保存と、同じ実全関手射への写像を使う。
規約：元の指定値と全 Hom 自然性を保つ。使われ方：指定合成子 α の二変数自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
variable {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
local notation "P₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P
local notation "P₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'
local notation "Q₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q
local notation "Q₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'
local notation "I" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))
/-- 同じ双加群二変数の作用の実像は、指定された二つの一変数の作用へ分かれる。 -/
lemma dgKernelBimoduleNerveMap_factor (f : P ⟶ P') (g : Q ⟶ Q') :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) g
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f (𝟙 I))) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (𝟙 Q)
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f (𝟙 I))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) g
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P₁)))) := by
  have h := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_comp R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (𝟙 Q) g
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f (𝟙 I)) (𝟙 _)
  simpa only [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp] using!
    congrArg (fun m => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map m) h
/-- 同じ逆結合子の自然性は、二つの指定変数の実作用を通る経路に一致する。 -/
lemma dgKernelInverseAssociatorNerve_naturality_factor (f : P ⟶ P') (g : Q ⟶ Q') :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R F E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q₀ P₀
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E D g f) (𝟙 I)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (𝟙 Q)
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) f (𝟙 I))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) g
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P₁)))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R F E D (_root_.SerrePositivity.DifferentialGraded.RightModule R D) Q₁ P₁
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).inv := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleNerve_inverse_associator_naturality R F E D (RightModule R D)
    g f (𝟙 I)
  rw [dgKernelBimoduleNerveMap_factor R D E F f g] at h
  simpa only [Category.assoc] using! h
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
