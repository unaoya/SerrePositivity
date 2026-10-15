module
public import SerrePositivity.DifferentialGraded.Tensor.Interchange
public import SerrePositivity.DifferentialGraded.Tensor.YonedaNaturality

/-! # balanced tensorのYoneda評価の主Homに関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右representableのYoneda評価は主Hom複体全体に関して自然。 -/
lemma yonedaEvaluation_enriched_naturality (z : D) (N N' : LeftModule A D) :
    leftHomMap A D (representable A z) N N' ≫
      homPostcompose (obj A D (representable A z) N) (yonedaEvaluation A D z N') =
    leftModuleHomπ A D N N' z ≫
      homPrecompose (yonedaEvaluation A D z N) (N'.obj z) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro τ
  change (homPostcompose _ (yonedaEvaluation A D z N')).f q
      ((leftHomMap A D (representable A z) N N').f q τ) =
    (homPrecompose (yonedaEvaluation A D z N) _).f q ((leftModuleHomπ A D N N' z).f q τ)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D (representable A z) N
  intro x p r a n ha hn f m
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (yonedaEvaluation A D z N').f n
      (((leftHomMap A D (representable A z) N N').f q τ).v a n hn
        (element A D (representable A z) N x f m ha)) =
    ((leftModuleHomπ A D N N' z).f q τ).v a n hn
      ((yonedaEvaluation A D z N).f a (element A D (representable A z) N x f m ha))
  rw [leftHomMap_element_of_sum A D (representable A z) τ x f m ha rfl hn]
  simp only [Units.smul_def, map_zsmul]
  exact (yonedaEvaluation_homElement A D τ z x f m ha (by omega) hn).symm

/-- 左representableのYoneda評価も主Hom複体全体に関して自然。 -/
lemma leftYonedaEvaluation_enriched_naturality (z : D) (M M' : RightModule A D) :
    rightHomMap A D M M' (leftRepresentable A z) ≫
      homPostcompose (obj A D M (leftRepresentable A z)) (leftYonedaEvaluation A D z M') =
    moduleHomπ A D M M' z ≫
      homPrecompose (leftYonedaEvaluation A D z M) (M'.obj (op z)) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro τ
  change (homPostcompose _ (leftYonedaEvaluation A D z M')).f q
      ((rightHomMap A D M M' (leftRepresentable A z)).f q τ) =
    (homPrecompose (leftYonedaEvaluation A D z M) _).f q ((moduleHomπ A D M M' z).f q τ)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D M (leftRepresentable A z)
  intro x r p a n ha hn m f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (leftYonedaEvaluation A D z M').f n
      (((rightHomMap A D M M' (leftRepresentable A z)).f q τ).v a n hn
        (element A D M (leftRepresentable A z) x m f ha)) =
    ((moduleHomπ A D M M' z).f q τ).v a n hn
      ((leftYonedaEvaluation A D z M).f a (element A D M (leftRepresentable A z) x m f ha))
  rw [rightHomMap_element_of_sum A D (leftRepresentable A z) τ x m f ha rfl hn]
  exact (leftYonedaEvaluation_homElement A D τ z x m f ha (by omega) hn).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
