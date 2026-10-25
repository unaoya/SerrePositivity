module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointComparison
public import SerrePositivity.InfinityCategories.Stable.IdentityCocone
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterFaces
/-!
概要：指定 native 余錐の一点下への回収は、実際の恒等余錐に一致する。
方針：全 native 成分から回収した Hom の単位性で実辺を同定する。
規約：頂点の同型だけでなく、実 coslice の零単体の等号を証明する。
使われ方：固定終点での標準 Hom の族を恒等余錐と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredSimplex_native :
    dgCoherentBarCoconeRecoveredSimplex R D F hMC
      (dgCoherentBarNormalizedNativeCocone R D F hMC) =
    InfinityCategories.PinchedHom.constant (dgCoherentBarNativeApex R D F hMC) 1 := by
  apply Simplex.ext
  change dgCoherentBarCoconeRecoveredRawData R D F hMC
    (dgCoherentBarNormalizedNativeCocone R D F hMC) = _
  apply dgCoherentBarJoinSimplexData_ext (n := 0) (m := 0)
  · rw [dgCoherentBarCoconeRecoveredRawData_left]
    change (dgCoherentBarNativeApex R D F hMC).toSimplexData =
      ((dgNerve R (RightModule R D)).map (SimplexCategory.mkHom
        (dgCoherentBarJoinLeft 0 0)).op
          (InfinityCategories.PinchedHom.constant
            (dgCoherentBarNativeApex R D F hMC) 1)).toSimplexData
    have h := InfinityCategories.PinchedHom.constant_pullback
      (X := dgNerve R (RightModule R D)) (x := dgCoherentBarNativeApex R D F hMC)
      (SimplexCategory.mkHom (dgCoherentBarJoinLeft 0 0))
    simpa only [InfinityCategories.PinchedHom.constant_zero] using
      (congrArg Simplex.toSimplexData h).symm
  · rw [dgCoherentBarCoconeRecoveredRawData_right]
    change (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex.toSimplexData = _
    rw [dgCoherentBarNormalizedNativeCocone_vertex]
    change (dgCoherentBarNativeApex R D F hMC).toSimplexData =
      ((dgNerve R (RightModule R D)).map (SimplexCategory.mkHom
        (dgCoherentBarJoinRight 0 0)).op
          (InfinityCategories.PinchedHom.constant
            (dgCoherentBarNativeApex R D F hMC) 1)).toSimplexData
    have h := InfinityCategories.PinchedHom.constant_pullback
      (X := dgNerve R (RightModule R D)) (x := dgCoherentBarNativeApex R D F hMC)
      (SimplexCategory.mkHom (dgCoherentBarJoinRight 0 0))
    simpa only [InfinityCategories.PinchedHom.constant_zero] using
      (congrArg Simplex.toSimplexData h).symm
  · intro K L hK hL a b k hJ ha hb hk
    have hK0 := dgCoherentBarFinOneSubset_eq_univ K hK
    have hL0 := dgCoherentBarFinOneSubset_eq_univ L hL
    subst K
    subst L
    have hSet := dgCoherentBarJoinSubset_univ 0 0
    have ha0 : a = 0 := by
      have h := ha
      simp only [hSet] at h
      exact h.trans (coherentDiagramTop_min 0).symm
    have hb0 : b = Fin.last 1 := by
      have h := hb
      simp only [hSet] at h
      exact h.trans (coherentDiagramTop_max 0).symm
    have hk0 : k = 0 := by
      rw [dgCoherentBarJoinSubset_card] at hk
      norm_num at hk
      exact hk
    have hFull := dgCoherentBarCoconeRecoveredRawData_full_hom_heq R D F hMC
      (dgCoherentBarNormalizedNativeCocone R D F hMC)
    have hUnit := (dgCoherentBarCoconeLiftHom_fixed R D F hMC
      (dgCoherentBarNativeApex R D F hMC) (dgCoherentBarNativeCoconePoint R D F hMC)).trans
        (dgCoherentBarNativeCoconePoint_hom R D F hMC)
    have hConstant := dgCoherentBarConstant_hom_unit (R := R) (C := RightModule R D)
      (dgCoherentBarNativeApex R D F hMC) (dgCoherentBarJoinSubset Finset.univ Finset.univ)
      a b k hJ ha hb hk (by rw [hSet]; simp)
    refine HEq.trans ?_ ((hFull.trans hUnit).trans hConstant.symm)
    exact SimplexData.hom_heq_of_indices_degree _ hSet ha0 hb0 hk0

lemma dgCoherentBarCoconePointComparison_native :
    (dgCoherentBarCoconePointComparison R D F hMC).app (Opposite.op ⦋0⦌)
      (dgCoherentBarNormalizedNativeCocone R D F hMC) =
        cosliceIdentityCone (dgCoherentBarNativeApex R D F hMC) := by
  apply Subtype.ext
  change (joinStdSimplexIso 0 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarCoconeRecoveredSimplex R D F hMC
        (dgCoherentBarNormalizedNativeCocone R D F hMC)) =
      SSet.const (dgCoherentBarNativeApex R D F hMC)
  rw [dgCoherentBarCoconeRecoveredSimplex_native]
  change (joinStdSimplexIso 0 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      ((dgNerve R (RightModule R D)).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
        (dgCoherentBarNativeApex R D F hMC)) = _
  rw [← SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_zero,
    SSet.comp_const, SSet.comp_const]

end SerrePositivity.InfinityCategories
