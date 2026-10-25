module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedCode
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSphereArrowLift
/-!
概要：κ個以下の全シフト自由 sphere 間閉射を、一つの係数コードへ同時に持ち上げる。
方針：各閉射の次数 n-m の係数を元の出発関手の全基底像に併合する。
規約：元の全 Hom の厳密因子化と、各持ち上げ閉射の係数評価の厳密一致を保持する。
使われ方：c′ の行有限自由行列の support 全体を共通源へ取り込む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (D : Type v) [DGCategory R D] [Small.{u} D]
  (value : Set.Iio a → D) (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (source target : K → Set.Iio a) (n m : K → ℤ)
  (f : ∀ k, freeSphere R D (value (source k)) (n k) ⟶
    freeSphere R D (value (target k)) (m k))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

def dgSphereFamilyCoefficient (k : K) :
    GradedHom R (value (source k)) (value (target k)) (n k - m k) :=
  freeSphereClosedCoefficient R D (value (source k)) (value (target k)) (n k) (m k) (f k)

local notation "S" => dgCodeAugmentedSource R κ c D value F source
local notation "T" => dgCodeAugmentedTarget R κ c D value F target
local notation "N" => dgCodeAugmentedDegree R κ c (fun k => n k - m k)
local notation "P" => dgCodeAugmentedCoefficient R κ c D value F source target
  (fun k => n k - m k) (dgSphereFamilyCoefficient R κ a D value source target n m f)
local notation "hB" => dgCodeAugmentedCoefficientIndex_cardinal_le R κ c hκ hK

def dgSphereFamilySourceCode : DGCategoryPresentationCode R κ :=
  DGGeneratedHomWord.code R D κ a S T N value P hκ hB

def dgSphereFamilySourceEvaluation : DGFunctor R
    ((dgSphereFamilySourceCode R κ c a D value F source target n m f hκ hK).Objects R κ) D :=
  DGGeneratedHomWord.codeEvaluation R D κ a S T N value P hκ hB

def dgSphereFamilySourceInclusion : DGFunctor R (c.Objects R κ)
    ((dgSphereFamilySourceCode R κ c a D value F source target n m f hκ hK).Objects R κ) :=
  dgAugmentedSourceCodeInclusion R κ c a D value F source target (fun k => n k - m k)
    (dgSphereFamilyCoefficient R κ a D value source target n m f) hκ hK

lemma dgSphereFamilySourceInclusion_comp_evaluation :
    (dgSphereFamilySourceInclusion R κ c a D value F source target n m f hκ hK).comp
      (dgSphereFamilySourceEvaluation R κ c a D value F source target n m f hκ hK) =
    F.comp (dgObjectImageEvaluation R value) :=
  dgAugmentedSourceCodeInclusion_comp_evaluation R κ c a D value F source target
    (fun k => n k - m k) (dgSphereFamilyCoefficient R κ a D value source target n m f) hκ hK

local notation "C" => (DGCategoryPresentationCode.Objects R κ
  (dgSphereFamilySourceCode R κ c a D value F source target n m f hκ hK))

def dgSphereFamilySourceArrow (k : K) :
    freeSphere R C (source k) (n k) ⟶ freeSphere R C (target k) (m k) :=
  DGGeneratedHomWord.codeFreeSphereClosedArrow R D κ a S T N value P hκ hB
    (source k) (target k) (n k) (m k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun k => n k - m k)
      (dgSphereFamilyCoefficient R κ a D value source target n m f) k)

lemma dgSphereFamilySourceArrow_coefficient_map (k : K) :
    ((dgSphereFamilySourceEvaluation R κ c a D value F source target n m f hκ hK).map
      (source k) (target k)).f (n k - m k)
      (freeSphereClosedCoefficient R C (source k) (target k) (n k) (m k)
        (dgSphereFamilySourceArrow R κ c a D value F source target n m f hκ hK k)) =
      freeSphereClosedCoefficient R D (value (source k)) (value (target k)) (n k) (m k) (f k) :=
  DGGeneratedHomWord.codeFreeSphereClosedArrow_coefficient_map R D κ a S T N value P hκ hB
    (source k) (target k) (n k) (m k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun k => n k - m k)
      (dgSphereFamilyCoefficient R κ a D value source target n m f) k)

end SerrePositivity.DifferentialGraded
