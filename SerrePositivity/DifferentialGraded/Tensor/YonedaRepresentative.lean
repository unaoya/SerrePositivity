module
public import SerrePositivity.DifferentialGraded.Tensor.YonedaEnriched
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Module.LeftYonedaFunctor

/-! # 代表対象を動かすYoneda tensor評価の全Hom自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma yonedaEvaluation_representative_naturality (N : LeftModule A D) (z z' : D) :
    yonedaHom A D z z' ≫ rightHomMap A D (representable A z) (representable A z') N ≫
      homPostcompose (obj A D (representable A z) N) (yonedaEvaluation A D z' N) =
    N.map z z' ≫ homPrecompose (yonedaEvaluation A D z N) (N.obj z') := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (homPostcompose _ (yonedaEvaluation A D z' N)).f k
      ((rightHomMap A D (representable A z) (representable A z') N).f k
        ((yonedaHom A D z z').f k f)) =
    (homPrecompose (yonedaEvaluation A D z N) _).f k ((N.map z z').f k f)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D (representable A z) N
  intro x r s a n ha hn h m
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (yonedaEvaluation A D z' N).f n
      (((rightHomMap A D (representable A z) (representable A z') N).f k
        ((yonedaHom A D z z').f k f)).v a n hn
          (element A D (representable A z) N x h m ha)) =
    ((N.map z z').f k f).v a n hn
      ((yonedaEvaluation A D z N).f a (element A D (representable A z) N x h m ha))
  rw [rightHomMap_element_of_sum A D N _ x h m ha rfl hn, yonedaHom_element,
    yonedaEvaluation_element, yonedaEvaluation_element]
  have hs : SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      ((k * r).negOnePow • forward A h f (show r + k = k + r by omega)) m (by omega) =
    (k * r).negOnePow • SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      (forward A h f (show r + k = k + r by omega)) m (by omega) := by
    simp only [SerrePositivity.DifferentialGraded.leftAction, Units.smul_def, map_zsmul]
    rfl
  rw [hs, SerrePositivity.DifferentialGraded.leftAction_forward A N h f m
    (show r + k = k + r by omega) (show s + r = a by omega) (by omega)]
  rw [mul_comm r k, smul_smul, Int.units_mul_self, one_smul]
  rfl

lemma leftYonedaEvaluation_representative_naturality (M : RightModule A D) (z z' : D) :
    leftYonedaHom A D z z' ≫ leftHomMap A D M (leftRepresentable A z) (leftRepresentable A z') ≫
      homPostcompose (obj A D M (leftRepresentable A z)) (leftYonedaEvaluation A D z' M) =
    M.map (op z) (op z') ≫
      homPrecompose (leftYonedaEvaluation A D z M) (M.obj (op z')) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (homPostcompose _ (leftYonedaEvaluation A D z' M)).f p
      ((leftHomMap A D M (leftRepresentable A z) (leftRepresentable A z')).f p
        ((leftYonedaHom A D z z').f p f)) =
    (homPrecompose (leftYonedaEvaluation A D z M) _).f p ((M.map (op z) (op z')).f p f)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D M (leftRepresentable A z)
  intro x r s a n ha hn m h
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (leftYonedaEvaluation A D z' M).f n
      (((leftHomMap A D M (leftRepresentable A z) (leftRepresentable A z')).f p
        ((leftYonedaHom A D z z').f p f)).v a n hn
          (element A D M (leftRepresentable A z) x m h ha)) =
    ((M.map (op z) (op z')).f p f).v a n hn
      ((leftYonedaEvaluation A D z M).f a (element A D M (leftRepresentable A z) x m h ha))
  rw [leftHomMap_element_of_sum A D M _ x m h ha rfl hn, leftYonedaHom_element]
  simp only [Units.smul_def, map_zsmul]
  rw [leftYonedaEvaluation_element, leftYonedaEvaluation_element]
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • ((r * (p + s)).negOnePow •
      moduleAction A M (x := op x) (y := op z')
        (forward A (D := D) (x := z') (y := z) (z := x) f h (by omega)) m (by omega)) =
    (r * s).negOnePow • moduleAction A M f (moduleAction A M h m ha) hn
  have hc := moduleAction_representable A x M (op z) (op z') p s r (p + s) n a
    (by omega) ha (by omega) f h m
  change moduleAction A M (x := op x) (y := op z')
    (forward A (D := D) (x := z') (y := z) (z := x) f h (by omega)) m (by omega) = _ at hc
  rw [hc]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : p * r + r * (p + s) = r * s + 2 * (p * r) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity.DifferentialGraded.BalancedTensor
