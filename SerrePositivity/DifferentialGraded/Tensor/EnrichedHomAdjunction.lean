module
public import SerrePositivity.DifferentialGraded.Tensor.ParameterTensorFamilies
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionFamilies
public import SerrePositivity.DifferentialGraded.Complexes.CurryingNaturality

/-! # パラメータ複体を持つtensor–Hom同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- パラメータ付きbalanced族と右Hom加群への豊穣自然変換の同値。 -/
def paramTransEquiv (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) :
    ParamFamily A D M N K T ≃ ModuleParamTrans A D K M (homRightModule A D N T) :=
  (paramTensorFamilyEquiv A D K M N T).trans
    ((balancedFamilyMapEquiv A D (tensorModule K M) N T).trans
      (tensorFamilyEquiv A K M (homRightModule A D N T)))

lemma paramTransEquiv_app (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) (a : ParamFamily A D M N K T) (x : D) :
    (paramTransEquiv A D K M N T a).app (op x) =
      curryRight (curryRight ((α_ K (M.obj (op x)) (N.obj x)).hom ≫ a.val x)) := rfl

variable [Small.{u} D]

/-- 任意Kからの射についての主Hom複体のtensor–Hom同値。 -/
def enrichedTensorHomEquiv (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) :
    (K ⟶ homComplex A (obj A D M N) T) ≃ (K ⟶ moduleHom A D M (homRightModule A D N T)) :=
  (tensorRightHomEquiv (obj A D M N) K T).symm.trans
    ((paramHomEquiv A D M N K T).trans
      ((paramTransEquiv A D K M N T).trans
        (moduleHomEquiv A D K M (homRightModule A D N T)).symm))

@[reassoc]
lemma enrichedTensorHomEquiv_π (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) (f : K ⟶ homComplex A (obj A D M N) T) (x : D) :
    enrichedTensorHomEquiv A D K M N T f ≫ moduleHomπ A D M (homRightModule A D N T) x =
      curryRight (curryRight ((α_ K (M.obj (op x)) (N.obj x)).hom ≫
        ((K ◁ ι A D M N x) ≫ uncurryRight f))) :=
  moduleHomEquiv_symm_π A D K M (homRightModule A D N T)
    (paramTransEquiv A D K M N T (paramRestrict A D M N (uncurryRight f))) x

lemma enrichedTensorHomEquiv_naturality_param {K L : Complex A} (M : RightModule A D)
    (N : LeftModule A D) (T : Complex A) (g : L ⟶ K)
    (f : K ⟶ homComplex A (obj A D M N) T) :
    enrichedTensorHomEquiv A D L M N T (g ≫ f) =
      g ≫ enrichedTensorHomEquiv A D K M N T f := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, enrichedTensorHomEquiv_π, enrichedTensorHomEquiv_π,
    curryRight_twice_precompose, uncurryRight_precompose]
  congr 2
  rw [associator_naturality_left_assoc, whisker_exchange_assoc]

/-- balanced tensorのHomと右Hom加群の主Hom endとの実際のchain iso。 -/
def enrichedTensorHomIso (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    homComplex A (obj A D M N) T ≅ moduleHom A D M (homRightModule A D N T) where
  hom := enrichedTensorHomEquiv A D _ M N T (𝟙 _)
  inv := (enrichedTensorHomEquiv A D _ M N T).symm (𝟙 _)
  hom_inv_id := by
    apply (enrichedTensorHomEquiv A D _ M N T).injective
    rw [enrichedTensorHomEquiv_naturality_param, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h := enrichedTensorHomEquiv_naturality_param A D M N T
      ((enrichedTensorHomEquiv A D _ M N T).symm (𝟙 _)) (𝟙 _)
    rw [Category.comp_id, Equiv.apply_symm_apply] at h
    exact h.symm

lemma enrichedTensorHomEquiv_eq_comp (K : Complex A) (M : RightModule A D)
    (N : LeftModule A D) (T : Complex A) (f : K ⟶ homComplex A (obj A D M N) T) :
    enrichedTensorHomEquiv A D K M N T f = f ≫ (enrichedTensorHomIso A D M N T).hom := by
  have h := enrichedTensorHomEquiv_naturality_param A D M N T f (𝟙 _)
  rw [Category.comp_id] at h
  exact h

end SerrePositivity.DifferentialGraded.BalancedTensor
