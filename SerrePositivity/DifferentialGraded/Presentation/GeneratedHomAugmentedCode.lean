module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedCoefficients
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCodeFunctorLift
/-!
概要：追加κ個以下の斉次係数を含み、元の出発 dg 関手を厳密に因子化するコードを構成する。
方針：元の全基底像と追加係数を併合し、κ自由被覆と全 Hom 同型による持ち上げを合成する。
規約：元の対象ラベルと全 Hom 作用を保持し、任意閉射の係数選択は別工程とする。
使われ方：c′ の共通出発提示の係数精密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (D : Type v) [DGCategory R D] (value : Set.Iio a → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (extraSource extraTarget : K → Set.Iio a) (extraDegree : K → ℤ)
  (extraCoefficient : ∀ k, GradedHom R (value (extraSource k)) (value (extraTarget k)) (extraDegree k))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

local notation "S" => dgCodeAugmentedSource R κ c D value F extraSource
local notation "T" => dgCodeAugmentedTarget R κ c D value F extraTarget
local notation "N" => dgCodeAugmentedDegree R κ c extraDegree
local notation "P" => dgCodeAugmentedCoefficient R κ c D value F
  extraSource extraTarget extraDegree extraCoefficient
local notation "hB" => dgCodeAugmentedCoefficientIndex_cardinal_le R κ c hκ hK

def dgAugmentedSourceCode : DGCategoryPresentationCode R κ :=
  DGGeneratedHomWord.code R D κ a S T N value P hκ hB

def dgAugmentedSourceCodeEvaluation : DGFunctor R
    ((dgAugmentedSourceCode R κ c a D value F extraSource extraTarget extraDegree
      extraCoefficient hκ hK).Objects R κ) D :=
  DGGeneratedHomWord.codeEvaluation R D κ a S T N value P hκ hB

def dgAugmentedSourceCodeInclusion : DGFunctor R (c.Objects R κ)
    ((dgAugmentedSourceCode R κ c a D value F extraSource extraTarget extraDegree
      extraCoefficient hκ hK).Objects R κ) :=
  DGGeneratedHomWord.codeFunctorLift R D κ a S T N value P hκ hB
    (c.Objects R κ) F
    (dgCodeAugmentedImage_contains R κ c D value F extraSource extraTarget extraDegree extraCoefficient)

lemma dgAugmentedSourceCodeInclusion_comp_evaluation :
    (dgAugmentedSourceCodeInclusion R κ c a D value F extraSource extraTarget extraDegree
      extraCoefficient hκ hK).comp
      (dgAugmentedSourceCodeEvaluation R κ c a D value F extraSource extraTarget extraDegree
        extraCoefficient hκ hK) = F.comp (dgObjectImageEvaluation R value) :=
  DGGeneratedHomWord.codeFunctorLift_comp_evaluation R D κ a S T N value P hκ hB
    (c.Objects R κ) F
    (dgCodeAugmentedImage_contains R κ c D value F extraSource extraTarget extraDegree extraCoefficient)

end SerrePositivity.DifferentialGraded
