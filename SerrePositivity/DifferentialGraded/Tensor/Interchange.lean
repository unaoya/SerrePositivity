module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

/-! # balanced tensorの左右作用の全次数交換則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左右のHom作用を交換する際の符号は二つのHom次数の積。 -/
lemma homMaps_interchange {M M' : RightModule A D} {N N' : LeftModule A D} {p q k : ℤ}
    (τ : (moduleHom A D M M').X p) (σ : (leftModuleHom A D N N').X q) (hk : p + q = k) :
    (((rightHomMap A D M M' N).f p τ).comp ((leftHomMap A D M' N N').f q σ) hk) =
    (p * q).negOnePow • (((leftHomMap A D M N N').f q σ).comp
      ((rightHomMap A D M M' N').f p τ) (by omega)) := by
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [Cochain.comp_v _ _ hk a (p + r + s) n (by omega) (by omega),
    Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) a (r + (q + s)) n (by omega) (by omega)]
  change (((leftHomMap A D M' N N').f q σ).v (p + r + s) n (by omega)
      ((((rightHomMap A D M M' N).f p τ).v a (p + r + s) (by omega))
        (element A D M N x m v ha))) =
    (p * q).negOnePow • (((rightHomMap A D M M' N').f p τ).v (r + (q + s)) n
      (by omega) ((((leftHomMap A D M N N').f q σ).v a (r + (q + s)) (by omega))
        (element A D M N x m v ha)))
  rw [rightHomMap_element_of_sum A D N τ x m v ha rfl (by omega),
    leftHomMap_element_of_sum A D M' σ x _ v rfl rfl (by omega),
    leftHomMap_element_of_sum A D M σ x m v ha rfl (by omega)]
  simp only [Units.smul_def, map_zsmul]
  change (q * (p + r)).negOnePow •
      element A D M' N' x
        (((moduleHomπ A D M M' x).f p τ).v r (p + r) (by omega) m)
        (((leftModuleHomπ A D N N' x).f q σ).v s (q + s) (by omega) v) (by omega) =
    (p * q).negOnePow • ((q * r).negOnePow •
      (((rightHomMap A D M M' N').f p τ).v (r + (q + s)) n (by omega)
        (element A D M N' x m
          (((leftModuleHomπ A D N N' x).f q σ).v s (q + s) (by omega) v) rfl)))
  rw [rightHomMap_element_of_sum A D N' τ x m _ rfl rfl (by omega)]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

end SerrePositivity.DifferentialGraded.BalancedTensor
