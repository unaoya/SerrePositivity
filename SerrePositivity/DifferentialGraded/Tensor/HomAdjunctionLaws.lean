module
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunction
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # tensor–Hom随伴の単位・余単位・三角恒等式と余極限保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite Limits CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorHomAdjunction_unit (N : LeftModule A D) (M : ModuleCategory A D) :
    (tensorHomAdjunction A D N).unit.app M =
      tensorHomEquiv A D M N (obj A D (ForgetEnrichment.to (Complex A) M) N) (𝟙 _) := by
  have h := ((tensorHomAdjunction A D N).homEquiv_id M).symm
  rw [tensorHomAdjunction_homEquiv] at h
  exact h

@[simp]
lemma tensorHomAdjunction_unit_eval (N : LeftModule A D) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((tensorHomAdjunction A D N).unit.app M) =
      curryRight (ι A D (ForgetEnrichment.to (Complex A) M) N x) := by
  rw [tensorHomAdjunction_unit]
  have h := tensorHomEquiv_eval A D M N
    (obj A D (ForgetEnrichment.to (Complex A) M) N) (𝟙 _) x
  rw [Category.comp_id] at h
  exact h

lemma tensorHomAdjunction_counit (N : LeftModule A D) (T : Complex A) :
    (tensorHomAdjunction A D N).counit.app T =
      (tensorHomEquiv A D (ForgetEnrichment.of (Complex A) (homRightModule A D N T)) N T).symm
        (𝟙 _) := by
  have h := ((tensorHomAdjunction A D N).homEquiv_symm_id T).symm
  rw [tensorHomAdjunction_homEquiv] at h
  exact h

@[reassoc (attr := simp)]
lemma ι_tensorHomAdjunction_counit (N : LeftModule A D) (T : Complex A) (x : D) :
    ι A D (homRightModule A D N T) N x ≫ (tensorHomAdjunction A D N).counit.app T =
      uncurryRight (𝟙 (homComplex A (N.obj x) T)) := by
  rw [tensorHomAdjunction_counit]
  have h := ι_tensorHomEquiv_symm A D
    (ForgetEnrichment.of (Complex A) (homRightModule A D N T)) N T (𝟙 _) x
  rw [CategoryTheory.Functor.map_id] at h
  exact h

lemma tensorHomAdjunction_counit_element (N : LeftModule A D) (T : Complex A) (x : D)
    {r s n : ℤ} (g : Homogeneous (N.obj x) T r) (v : (N.obj x).X s) (hn : r + s = n) :
    ((tensorHomAdjunction A D N).counit.app T).f n
      (element A D (homRightModule A D N T) N x g v hn) = g.v s n (by omega) v := by
  have h := element_postcompose A D (homRightModule A D N T) N x
    ((tensorHomAdjunction A D N).counit.app T) (uncurryRight (𝟙 (homComplex A (N.obj x) T)))
    (ι_tensorHomAdjunction_counit A D N T x) g v hn
  exact h.trans (uncurryRight_apply (𝟙 (homComplex A (N.obj x) T)) r s n hn g v)

lemma tensorHomAdjunction_left_triangle (N : LeftModule A D) (M : ModuleCategory A D) :
    (rightTensorFunctor A D N).map ((tensorHomAdjunction A D N).unit.app M) ≫
      (tensorHomAdjunction A D N).counit.app ((rightTensorFunctor A D N).obj M) = 𝟙 _ :=
  (tensorHomAdjunction A D N).left_triangle_components M

lemma tensorHomAdjunction_right_triangle (N : LeftModule A D) (T : Complex A) :
    (tensorHomAdjunction A D N).unit.app ((homRightFunctor A D N).obj T) ≫
      (homRightFunctor A D N).map ((tensorHomAdjunction A D N).counit.app T) = 𝟙 _ :=
  (tensorHomAdjunction A D N).right_triangle_components T

/-- 固定左加群とのbalanced tensorは、存在する任意サイズの余極限を保存する。 -/
instance rightTensorFunctor_preservesColimits (N : LeftModule A D) :
    PreservesColimitsOfSize.{w, t} (rightTensorFunctor A D N) :=
  (tensorHomAdjunction A D N).leftAdjoint_preservesColimits

end SerrePositivity.DifferentialGraded.BalancedTensor
