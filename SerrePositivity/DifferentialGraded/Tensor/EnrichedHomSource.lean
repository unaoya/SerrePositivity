module
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomElements
public import SerrePositivity.DifferentialGraded.Tensor.HomElements
public import SerrePositivity.DifferentialGraded.Complexes.HomContravariant
public import SerrePositivity.DifferentialGraded.Module.Precomposition

/-! # 豊穣tensor–Hom同型の右加群Hom変数の反変自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右加群Mの全Homについて、豊穣転置は符号付き前合成を保つ。 -/
lemma enrichedTensorHomIso_source_naturality (M M' : RightModule A D) (N : LeftModule A D)
    (T : Complex A) :
    (rightHomMap A D M M' N ≫ (homContravariantDG A T).map
      (op (obj A D M' N)) (op (obj A D M N))) ≫
      homPostcompose (homComplex A (obj A D M' N) T) (enrichedTensorHomIso A D M N T).hom =
    modulePrecompositionMap A D M M' (homRightModule A D N T) ≫
      homPrecompose (enrichedTensorHomIso A D M' N T).hom
        (moduleHom A D M (homRightModule A D N T)) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro σ
  change (homPostcompose _ (enrichedTensorHomIso A D M N T).hom).f p
      (((homContravariantDG A T).map (op (obj A D M' N)) (op (obj A D M N))).f p
        ((rightHomMap A D M M' N).f p σ)) =
    (homPrecompose (enrichedTensorHomIso A D M' N T).hom _).f p
      ((modulePrecompositionMap A D M M' (homRightModule A D N T)).f p σ)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change (enrichedTensorHomIso A D M N T).hom.f n
      ((((homContravariantDG A T).map (op (obj A D M' N)) (op (obj A D M N))).f p
        ((rightHomMap A D M M' N).f p σ)).v q n hn f) =
    ((modulePrecompositionMap A D M M' (homRightModule A D N T)).f p σ).v q n hn
      ((enrichedTensorHomIso A D M' N T).hom.f q f)
  rw [homContravariantDG_map_element, modulePrecompositionMap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • (enrichedTensorHomIso A D M N T).hom.f n
      (((rightHomMap A D M M' N).f p σ).comp f (by omega)) =
    forward A (D := RightModule A D) σ ((enrichedTensorHomIso A D M' N T).hom.f q f)
      (by omega)
  apply moduleHomElement_ext A D
  intro x
  simp only [Units.smul_def, map_zsmul]
  rw [moduleHomForward_π]
  change (p * q).negOnePow •
      (moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((rightHomMap A D M M' N).f p σ).comp f (by omega))) =
    (p * q).negOnePow • (((moduleHomπ A D M M' x).f p σ).comp
      ((moduleHomπ A D M' (homRightModule A D N T) x).f q
        ((enrichedTensorHomIso A D M' N T).hom.f q f)) (by omega))
  congr 1
  apply Cochain.ext
  intro r l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [Cochain.comp_v _ _ (by omega : p + q = n) r (r + p) l rfl (by omega)]
  simp only [ModuleCat.comp_apply]
  apply Cochain.ext
  intro s a ha
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [enrichedTensorHomIso_hom_element, enrichedTensorHomIso_hom_element]
  rw [Cochain.comp_v _ f (by omega : p + q = n) (r + s) (r + p + s) a (by omega) (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [rightHomMap_element_of_sum A D N (l := r + p) σ x m v rfl (by omega) (by omega)]

end SerrePositivity.DifferentialGraded.BalancedTensor
