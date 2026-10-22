module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofLayerInverse
public import SerrePositivity.KST.LocalizingInvariants.DGBimodulePostnikovHomCriterion

/-!
概要：細分した共通底の零切断上で、元の層逆の左右作用保存を判定する。
方針：実両層の厳密 −2 集中から作用を降ろし、同じ cochain 射の二条件を比較する。
規約：その条件が成立するとはまだ主張しない。使われ方：π₀・π₂ による逆の追加補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  {k : ℕ} (hm : m ≤ k)

local instance roofZeroBase_nonpositive :
    (postnikovOneRoofRefine R f c hm).roof.apex.X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c hm).roof_nonpositive

local instance roofZeroDenominator_lowerBound :
    (postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c hm)).X.IsStrictlyGE (-2) :=
  postnikovOneRoofDenominatorLayer_lowerBound R f _

local instance roofZeroDenominator_upperBound :
    (postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c hm)).X.IsStrictlyLE (-2) :=
  postnikovOneRoofDenominatorLayer_upperBound R f _

local instance roofZeroNumerator_lowerBound :
    (postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c hm)).X.IsStrictlyGE (-2) :=
  postnikovOneRoofNumeratorLayer_lowerBound R f _

local instance roofZeroNumerator_upperBound :
    (postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c hm)).X.IsStrictlyLE (-2) :=
  postnikovOneRoofNumeratorLayer_upperBound R f _

def postnikovRoofDenominatorZeroBimodule :
    Bimod (postnikov R (postnikovOneRoofRefine R f c hm).roof.apex 0)
      (postnikov R (postnikovOneRoofRefine R f c hm).roof.apex 0) :=
  postnikovBimodule R _ (postnikovOneRoofDenominatorLayer R f
    (postnikovOneRoofRefine R f c hm)) (-2) 0 (by omega)

def postnikovRoofNumeratorZeroBimodule :
    Bimod (postnikov R (postnikovOneRoofRefine R f c hm).roof.apex 0)
      (postnikov R (postnikovOneRoofRefine R f c hm).roof.apex 0) :=
  postnikovBimodule R _ (postnikovOneRoofNumeratorLayer R f
    (postnikovOneRoofRefine R f c hm)) (-2) 0 (by omega)

lemma postnikovRoofLayerInverse_left_action_iff
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2)) :
    (postnikovRoofDenominatorZeroBimodule R f c hm).actLeft ≫
        postnikovRoofLayerInverse R f c hm r =
      ((postnikov R (postnikovOneRoofRefine R f c hm).roof.apex 0).X ◁
        postnikovRoofLayerInverse R f c hm r) ≫
          (postnikovRoofNumeratorZeroBimodule R f c hm).actLeft ↔
    (postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c hm)).actLeft ≫
        postnikovRoofLayerInverse R f c hm r =
      ((postnikovOneRoofRefine R f c hm).roof.apex.X ◁
        postnikovRoofLayerInverse R f c hm r) ≫
          (postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c hm)).actLeft :=
  postnikovBimodule_left_hom_iff R _ _ _ (-2) 0 (by omega) _

lemma postnikovRoofLayerInverse_right_action_iff
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2)) :
    (postnikovRoofDenominatorZeroBimodule R f c hm).actRight ≫
        postnikovRoofLayerInverse R f c hm r =
      (postnikovRoofLayerInverse R f c hm r ▷
        (postnikov R (postnikovOneRoofRefine R f c hm).roof.apex 0).X) ≫
          (postnikovRoofNumeratorZeroBimodule R f c hm).actRight ↔
    (postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c hm)).actRight ≫
        postnikovRoofLayerInverse R f c hm r =
      (postnikovRoofLayerInverse R f c hm r ▷
        (postnikovOneRoofRefine R f c hm).roof.apex.X) ≫
          (postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c hm)).actRight :=
  postnikovBimodule_right_hom_iff R _ _ _ (-2) 0 (by omega) _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
