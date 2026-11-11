module
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.Algebra.Homology.QuasiIso

/-! # 単位を始点とする実 Hom 複体の自然同型

概要：任意の複体を単位からの Hom 複体として、鎖写像も含めて自然に実現する。
方針：閉モノイダル圏の単位同型を主 Hom 複体へ特殊化する。
規約：全次数の鎖同型。使われ方：任意 Hom 鎖写像の pinched 比較の中間模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 任意複体から単位を始点とする実 Hom 複体への鎖同型。 -/
def complexUnitHomIso (K : Complex A) : K ≅ homComplex A (𝟙_ (Complex A)) K :=
  (MonoidalClosed.unitNatIso (C := Complex A)).app K

/-- 単位 Hom の実同型は任意の chain map に関して自然。 -/
lemma complexUnitHomIso_naturality {K L : Complex A} (φ : K ⟶ L) :
    (complexUnitHomIso K).hom ≫ homPostcompose (𝟙_ (Complex A)) φ =
      φ ≫ (complexUnitHomIso L).hom :=
  ((MonoidalClosed.unitNatIso (C := Complex A)).hom.naturality φ).symm

/-- 単位 Hom による後合成は、同じ鎖写像の実同型による共役。 -/
lemma complexUnitHomPostcompose_eq {K L : Complex A} (φ : K ⟶ L) :
    homPostcompose (𝟙_ (Complex A)) φ =
      (complexUnitHomIso K).inv ≫ φ ≫ (complexUnitHomIso L).hom := by
  rw [← complexUnitHomIso_naturality, Iso.inv_hom_id_assoc]

/-- 次数ごと全射な鎖写像の単位 Hom による後合成も次数ごと全射。 -/
lemma complexUnitHomPostcompose_surjective {K L : Complex A} (φ : K ⟶ L)
    (hs : ∀ i, Function.Surjective (φ.f i)) (i : ℤ) :
    Function.Surjective ((homPostcompose (𝟙_ (Complex A)) φ).f i) := by
  rw [complexUnitHomPostcompose_eq]
  exact ((ConcreteCategory.bijective_of_isIso ((complexUnitHomIso L).hom.f i)).2.comp
    ((hs i).comp (ConcreteCategory.bijective_of_isIso ((complexUnitHomIso K).inv.f i)).2))

/-- 準同型な鎖写像の単位 Hom による後合成も準同型。 -/
lemma complexUnitHomPostcompose_quasiIso {K L : Complex A} (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (homPostcompose (𝟙_ (Complex A)) φ) := by
  rw [complexUnitHomPostcompose_eq]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
