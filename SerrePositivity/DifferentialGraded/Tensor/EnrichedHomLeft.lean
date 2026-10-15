module
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomElements
public import SerrePositivity.DifferentialGraded.Tensor.HomElements
public import SerrePositivity.DifferentialGraded.Module.HomRightContraMaps
public import SerrePositivity.DifferentialGraded.Module.Postcomposition

/-! # 豊穣tensor–Hom同型の左加群Hom変数の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群Nの全Homについて、豊穣転置は右Hom加群の反変作用と整合する。 -/
lemma enrichedTensorHomIso_left_naturality (M : RightModule A D) (N N' : LeftModule A D)
    (T : Complex A) :
    (leftHomMap A D M N N' ≫ (homContravariantDG A T).map
      (op (obj A D M N')) (op (obj A D M N))) ≫
      homPostcompose (homComplex A (obj A D M N') T) (enrichedTensorHomIso A D M N T).hom =
    (homRightContraHomMap A D N N' T ≫ modulePostcompositionMap A D M
      (homRightModule A D N' T) (homRightModule A D N T)) ≫
      homPrecompose (enrichedTensorHomIso A D M N' T).hom
        (moduleHom A D M (homRightModule A D N T)) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro σ
  change (homPostcompose _ (enrichedTensorHomIso A D M N T).hom).f p
      (((homContravariantDG A T).map (op (obj A D M N')) (op (obj A D M N))).f p
        ((leftHomMap A D M N N').f p σ)) =
    (homPrecompose (enrichedTensorHomIso A D M N' T).hom _).f p
      ((modulePostcompositionMap A D M (homRightModule A D N' T)
        (homRightModule A D N T)).f p ((homRightContraHomMap A D N N' T).f p σ))
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change Homogeneous (obj A D M N') T q at f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change (enrichedTensorHomIso A D M N T).hom.f n
      ((((homContravariantDG A T).map (op (obj A D M N')) (op (obj A D M N))).f p
        ((leftHomMap A D M N N').f p σ)).v q n hn f) =
    (((modulePostcompositionMap A D M (homRightModule A D N' T)
      (homRightModule A D N T)).f p ((homRightContraHomMap A D N N' T).f p σ)).v q n hn)
      ((enrichedTensorHomIso A D M N' T).hom.f q f)
  rw [homContravariantDG_map_element, modulePostcompositionMap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • (enrichedTensorHomIso A D M N T).hom.f n
      (((leftHomMap A D M N N').f p σ).comp f (by omega)) =
    compose A (D := RightModule A D) ((homRightContraHomMap A D N N' T).f p σ)
      ((enrichedTensorHomIso A D M N' T).hom.f q f) hn
  apply moduleHomElement_ext A D
  intro x
  simp only [Units.smul_def, map_zsmul]
  rw [moduleHomCompose_π]
  change (p * q).negOnePow •
      (moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((leftHomMap A D M N N').f p σ).comp f (by omega))) =
    ((moduleHomπ A D M (homRightModule A D N' T) x).f q
      ((enrichedTensorHomIso A D M N' T).hom.f q f)).comp
      ((moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x).f p
        ((homRightContraHomMap A D N N' T).f p σ)) hn
  apply Cochain.ext
  intro r l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ hn r (r + q) l rfl (by omega)]
  change (p * q).negOnePow •
      (((moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((leftHomMap A D M N N').f p σ).comp f (by omega)))).v r l hl m) =
    (((moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x).f p
      ((homRightContraHomMap A D N N' T).f p σ)).v (r + q) l (by omega))
      (((moduleHomπ A D M (homRightModule A D N' T) x).f q
        ((enrichedTensorHomIso A D M N' T).hom.f q f)).v r (r + q) rfl m)
  apply Cochain.ext
  intro s a ha
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (N.obj x).X s at v
  rw [Cochain.units_smul_v, homRightContraHomMap_element, Cochain.units_smul_v]
  change (p * q).negOnePow •
      ((((moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((leftHomMap A D M N N').f p σ).comp f (by omega)))).v r l hl m).v s a ha v) =
    (p * (r + q)).negOnePow •
      ((((leftModuleHomπ A D N N' x).f p σ).comp
        (((moduleHomπ A D M (homRightModule A D N' T) x).f q
          ((enrichedTensorHomIso A D M N' T).hom.f q f)).v r (r + q) rfl m)
        (by omega)).v s a ha v)
  rw [enrichedTensorHomIso_hom_element]
  rw [Cochain.comp_v _ f (by omega : p + q = n) (r + s) (r + (p + s)) a
    (by omega) (by omega), Cochain.comp_v _ _ (by omega : p + (r + q) = l) s (p + s) a
      (by omega) (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [leftHomMap_element_of_sum A D M (l := p + s) σ x m v rfl rfl (by omega)]
  have he := enrichedTensorHomIso_hom_element A D M N' T x (k := q) (r := r)
    (l := r + q) (s := p + s) (n := a) rfl (by omega) f m
    (((leftModuleHomπ A D N N' x).f p σ).v s (p + s) (by omega) v)
  refine Eq.trans ?_ (congrArg (fun z => (p * (r + q)).negOnePow • z) he).symm
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • ((p * r).negOnePow •
      f.v (r + (p + s)) a (by omega)
        (element A D M N' x m (((leftModuleHomπ A D N N' x).f p σ).v s (p + s) (by omega) v)
          rfl)) =
    (p * (r + q)).negOnePow • f.v (r + (p + s)) a (by omega)
      (element A D M N' x m (((leftModuleHomπ A D N N' x).f p σ).v s (p + s) (by omega) v) rfl)
  rw [smul_smul, ← Int.negOnePow_add]
  have hs : p * q + p * r = p * (r + q) := by ring
  rw [hs]

end SerrePositivity.DifferentialGraded.BalancedTensor
