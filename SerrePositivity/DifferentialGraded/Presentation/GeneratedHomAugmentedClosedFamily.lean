module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedCode
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomClosedLift
/-!
概要：κ個以下の元の閉射を同じ精密化コードへ同時に持ち上げる。
方針：各閉射の零 cycle を追加係数に取り、コードの閉射回収を適用する。
規約：元の dg 関手の全 Hom と、指定閉射の実評価を厳密に保持する。
使われ方：c′ の係数精密化の閉射族版。任意加群閉射の係数選択は別途必要。
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
  (source target : K → Set.Iio a)
  (f : ∀ k, ForgetEnrichment.of (Complex R) (value (source k)) ⟶
    ForgetEnrichment.of (Complex R) (value (target k)))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

def dgClosedFamilyCoefficient (k : K) : GradedHom R (value (source k)) (value (target k)) 0 :=
  (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f k))).val

local notation "S" => dgCodeAugmentedSource R κ c D value F source
local notation "T" => dgCodeAugmentedTarget R κ c D value F target
local notation "N" => dgCodeAugmentedDegree R κ c (fun _ : K => (0 : ℤ))
local notation "P" => dgCodeAugmentedCoefficient R κ c D value F source target
  (fun _ : K => (0 : ℤ)) (dgClosedFamilyCoefficient R κ a D value source target f)
local notation "hB" => dgCodeAugmentedCoefficientIndex_cardinal_le R κ c hκ hK

def dgClosedFamilySourceCode : DGCategoryPresentationCode R κ :=
  DGGeneratedHomWord.code R D κ a S T N value P hκ hB

def dgClosedFamilySourceEvaluation : DGFunctor R
    ((dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ) D :=
  DGGeneratedHomWord.codeEvaluation R D κ a S T N value P hκ hB

def dgClosedFamilySourceInclusion : DGFunctor R (c.Objects R κ)
    ((dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ) :=
  dgAugmentedSourceCodeInclusion R κ c a D value F source target (fun _ : K => 0)
    (dgClosedFamilyCoefficient R κ a D value source target f) hκ hK

lemma dgClosedFamilySourceInclusion_comp_evaluation :
    (dgClosedFamilySourceInclusion R κ c a D value F source target f hκ hK).comp
      (dgClosedFamilySourceEvaluation R κ c a D value F source target f hκ hK) =
    F.comp (dgObjectImageEvaluation R value) :=
  dgAugmentedSourceCodeInclusion_comp_evaluation R κ c a D value F source target
    (fun _ : K => 0) (dgClosedFamilyCoefficient R κ a D value source target f) hκ hK

def dgClosedFamilySourceArrow (k : K) :
    ForgetEnrichment.of (Complex R)
      (show (dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ
        from source k) ⟶
    ForgetEnrichment.of (Complex R)
      (show (dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ
        from target k) :=
  DGGeneratedHomWord.codeClosedLift R D κ a S T N value P hκ hB (source k) (target k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun _ : K => 0)
      (dgClosedFamilyCoefficient R κ a D value source target f) k)

lemma dgClosedFamilySourceArrow_map (k : K) :
    (dgClosedFamilySourceEvaluation R κ c a D value F source target f hκ hK).onClosed.map
      (dgClosedFamilySourceArrow R κ c a D value F source target f hκ hK k) = f k :=
  DGGeneratedHomWord.codeClosedLift_map R D κ a S T N value P hκ hB (source k) (target k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun _ : K => 0)
      (dgClosedFamilyCoefficient R κ a D value source target f) k)

end SerrePositivity.DifferentialGraded
