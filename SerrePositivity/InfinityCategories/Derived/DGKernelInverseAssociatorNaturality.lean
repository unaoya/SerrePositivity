module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleInverseAssociatorNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorIsoNerveAlgebra
/-!
概要：通常 kernel の逆結合子の自然性を、同じ二つの変数の作用へ分解する。
方針：元の composeMap の合成保存と、同じ実全関手射への写像を使う。
規約：元の指定値と全 Hom 自然性を保つ。使われ方：指定合成子 α の二変数自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
variable {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R F E}
local notation "P₀" => BimoduleCategory.underlying R E D P
local notation "P₁" => BimoduleCategory.underlying R E D P'
local notation "Q₀" => BimoduleCategory.underlying R F E Q
local notation "Q₁" => BimoduleCategory.underlying R F E Q'
local notation "I" => BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D))
/-- 同じ双加群二変数の作用の実像は、指定された二つの一変数の作用へ分かれる。 -/
lemma dgKernelBimoduleNerveMap_factor (f : P ⟶ P') (g : Q ⟶ Q') :
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.composeMap R F E (RightModule R D) g
        (BimoduleTensor.composeMap R E D (RightModule R D) f (𝟙 I))) =
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.composeMap R F E (RightModule R D) (𝟙 Q)
        (BimoduleTensor.composeMap R E D (RightModule R D) f (𝟙 I))) ≫
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.composeMap R F E (RightModule R D) g
        (𝟙 (BimoduleCategory.of R E (RightModule R D) (Morita.kernelTensor R D E P₁)))) := by
  have h := BimoduleTensor.composeMap_comp R F E (RightModule R D) (𝟙 Q) g
    (BimoduleTensor.composeMap R E D (RightModule R D) f (𝟙 I)) (𝟙 _)
  simpa only [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp] using!
    congrArg (fun m => (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map m) h
/-- 同じ逆結合子の自然性は、二つの指定変数の実作用を通る経路に一致する。 -/
lemma dgKernelInverseAssociatorNerve_naturality_factor (f : P ⟶ P') (g : Q ⟶ Q') :
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.associatorIso R F E D (RightModule R D) Q₀ P₀
        (DGFunctor.id (RightModule R D))).inv ≫
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.composeMap R F D (RightModule R D)
        (BimoduleTensor.composeMap R F E D g f) (𝟙 I)) =
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.composeMap R F E (RightModule R D) (𝟙 Q)
        (BimoduleTensor.composeMap R E D (RightModule R D) f (𝟙 I))) ≫
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.composeMap R F E (RightModule R D) g
        (𝟙 (BimoduleCategory.of R E (RightModule R D) (Morita.kernelTensor R D E P₁)))) ≫
    (dgBimoduleFunctorHomFunctor R F (RightModule R D)).map
      (BimoduleTensor.associatorIso R F E D (RightModule R D) Q₁ P₁
        (DGFunctor.id (RightModule R D))).inv := by
  have h := dgBimoduleNerve_inverse_associator_naturality R F E D (RightModule R D)
    g f (𝟙 I)
  rw [dgKernelBimoduleNerveMap_factor R D E F f g] at h
  simpa only [Category.assoc] using! h
end
end SerrePositivity.InfinityCategories
