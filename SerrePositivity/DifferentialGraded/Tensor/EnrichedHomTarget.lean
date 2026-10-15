module
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomElements
public import SerrePositivity.DifferentialGraded.Module.HomRightEnriched
public import SerrePositivity.DifferentialGraded.Module.Postcomposition

/-! # 豊穣tensor–Hom同型の終域Hom変数の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 終域Tの全Hom作用について、豊穣転置は後合成を保つ。 -/
lemma enrichedTensorHomIso_target_naturality (M : RightModule A D) (N : LeftModule A D)
    (T T' : Complex A) :
    (homCovariantDG A (obj A D M N)).map T T' ≫
      homPostcompose (homComplex A (obj A D M N) T) (enrichedTensorHomIso A D M N T').hom =
    (homRightHomMap A D N T T' ≫ modulePostcompositionMap A D M
      (homRightModule A D N T) (homRightModule A D N T')) ≫
      homPrecompose (enrichedTensorHomIso A D M N T).hom
        (moduleHom A D M (homRightModule A D N T')) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (homPostcompose _ (enrichedTensorHomIso A D M N T').hom).f p
      (((homCovariantDG A (obj A D M N)).map T T').f p t) =
    (homPrecompose (enrichedTensorHomIso A D M N T).hom _).f p
      ((modulePostcompositionMap A D M (homRightModule A D N T)
        (homRightModule A D N T')).f p ((homRightHomMap A D N T T').f p t))
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change (enrichedTensorHomIso A D M N T').hom.f n
      ((((homCovariantDG A (obj A D M N)).map T T').f p t).v q n hn f) =
    (((modulePostcompositionMap A D M (homRightModule A D N T)
      (homRightModule A D N T')).f p ((homRightHomMap A D N T T').f p t)).v q n hn)
        ((enrichedTensorHomIso A D M N T).hom.f q f)
  rw [homCovariantDG_map_element, modulePostcompositionMap_apply]
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π]
  apply Cochain.ext
  intro r l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [Cochain.comp_v _ _ hn r (r + q) l rfl (by omega)]
  simp only [ModuleCat.comp_apply]
  apply Cochain.ext
  intro s a ha
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [enrichedTensorHomIso_hom_element, homRightHomMap_element]
  rw [Cochain.comp_v f t hn (r + s) (r + s + q) a rfl (by omega)]
  rw [Cochain.comp_v _ t (by omega) s (r + s + q) a (by omega) (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [enrichedTensorHomIso_hom_element]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
