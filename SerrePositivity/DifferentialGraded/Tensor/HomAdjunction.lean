module
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionFamilies
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # balanced tensorと右Hom加群の随伴 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Hom endの閉零加群射を用いるtensor–Hom同値。 -/
def tensorHomEquiv (M : ModuleCategory A D) (N : LeftModule A D) (T : Complex A) :
    (obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T) ≃
      (M ⟶ ForgetEnrichment.of (Complex A) (homRightModule A D N T)) :=
  (homEquiv A D (ForgetEnrichment.to (Complex A) M) N T).trans
    ((balancedFamilyMapEquiv A D (ForgetEnrichment.to (Complex A) M) N T).trans
      (moduleMapFamilyEquiv A D M
        (ForgetEnrichment.of (Complex A) (homRightModule A D N T))).symm)

@[simp]
lemma tensorHomEquiv_eval (M : ModuleCategory A D) (N : LeftModule A D) (T : Complex A)
    (f : obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T) (x : D) :
    (moduleEvaluation A D x).map (tensorHomEquiv A D M N T f) =
      curryRight (ι A D (ForgetEnrichment.to (Complex A) M) N x ≫ f) :=
  moduleMorphismMk_eval A D _ _ x

@[reassoc (attr := simp)]
lemma ι_tensorHomEquiv_symm (M : ModuleCategory A D) (N : LeftModule A D) (T : Complex A)
    (g : M ⟶ ForgetEnrichment.of (Complex A) (homRightModule A D N T)) (x : D) :
    ι A D (ForgetEnrichment.to (Complex A) M) N x ≫ (tensorHomEquiv A D M N T).symm g =
      uncurryRight ((moduleEvaluation A D x).map g) := by
  exact ι_desc A D _ _ _ x

lemma tensorHomEquiv_naturality_target (M : ModuleCategory A D) (N : LeftModule A D)
    {T T' : Complex A} (f : obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T)
    (g : T ⟶ T') :
    tensorHomEquiv A D M N T' (f ≫ g) =
      tensorHomEquiv A D M N T f ≫ homRightModuleMap A D N g := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, tensorHomEquiv_eval, tensorHomEquiv_eval,
    homRightModuleMap_eval]
  rw [← Category.assoc, curryRight_naturality_target]

lemma tensorHomEquiv_naturality_source {M M' : ModuleCategory A D} (N : LeftModule A D)
    (h : M ⟶ M') (f : obj A D (ForgetEnrichment.to (Complex A) M') N ⟶ T) :
    tensorHomEquiv A D M N T
      (map A D h (𝟙 (ForgetEnrichment.of (Complex A) N)) ≫ f) =
      h ≫ tensorHomEquiv A D M' N T f := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, tensorHomEquiv_eval, tensorHomEquiv_eval]
  have hi := ι_map A D (N := ForgetEnrichment.of (Complex A) N)
    (N' := ForgetEnrichment.of (Complex A) N) h (𝟙 (ForgetEnrichment.of (Complex A) N)) x
  simp only [CategoryTheory.Functor.map_id] at hi
  change ι A D (ForgetEnrichment.to (Complex A) M) N x ≫
      map A D h (𝟙 (ForgetEnrichment.of (Complex A) N)) =
    ((moduleEvaluation A D x).map h ⊗ₘ 𝟙 (N.obj x)) ≫
      ι A D (ForgetEnrichment.to (Complex A) M') N x at hi
  rw [← Category.assoc, hi, Category.assoc]
  exact curryRight_naturality_source _ _

/-- 固定左加群とのbalanced tensorを閉零右加群圏上の通常関手にする。 -/
def rightTensorFunctor (N : LeftModule A D) : ModuleCategory A D ⥤ Complex A where
  obj M := obj A D (ForgetEnrichment.to (Complex A) M) N
  map h := map A D h (𝟙 (ForgetEnrichment.of (Complex A) N))
  map_id M := map_id A D M (ForgetEnrichment.of (Complex A) N)
  map_comp f g := by
    simpa only [Category.id_comp] using
      map_comp A D f g (𝟙 (ForgetEnrichment.of (Complex A) N))
        (𝟙 (ForgetEnrichment.of (Complex A) N))

/-- balanced tensorは右Hom加群関手の左随伴。 -/
def tensorHomAdjunction (N : LeftModule A D) :
    rightTensorFunctor A D N ⊣ homRightFunctor A D N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M T => tensorHomEquiv A D M N T
      homEquiv_naturality_left_symm := by
        intro M M' T f g
        change M' ⟶ ForgetEnrichment.of (Complex A) (homRightModule A D N T) at g
        change (tensorHomEquiv A D M N T).symm (f ≫ g) =
          map A D f (𝟙 (ForgetEnrichment.of (Complex A) N)) ≫
            (tensorHomEquiv A D M' N T).symm g
        apply (tensorHomEquiv A D M N T).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_source, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g => tensorHomEquiv_naturality_target A D _ N f g }

lemma tensorHomAdjunction_homEquiv (N : LeftModule A D) (M : ModuleCategory A D)
    (T : Complex A) :
    (tensorHomAdjunction A D N).homEquiv M T = tensorHomEquiv A D M N T := by
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) M) T

end SerrePositivity.DifferentialGraded.BalancedTensor
