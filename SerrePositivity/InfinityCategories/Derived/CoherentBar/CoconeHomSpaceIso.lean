module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseCoconeHomRecovery
/-!
概要：終点固定の全余錐空間と、正規化実 bar の実 pinched Hom の同型を構成する。
方針：逆余錐の全係数を回収し、両逆則を全部分集合の線形座標で確認する。
規約：全単体・全面・全退化での実同型。公開 MC を代入した無条件版も併設する。
使われ方：工程Bの全写像空間の普遍性の比較。
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
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeInverseSimplex_linear {n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) n) :
    dgCoherentBarCoconeLinearData R D F hMC y
      (dgCoherentBarCoconeInverseSimplex R D F hMC y f) = f.val := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change J.Nonempty at hJ
  change k = 1 - (J.card : ℤ) at hk
  let r := J.card - 1
  have hcJ : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hkr : k = -(r : ℤ) := by rw [hcJ] at hk; push_cast at hk; omega
  cases hkr
  change dgCoherentBarCoconeSubsetHom R D F hMC y
    (dgCoherentBarCoconeInverseSimplex R D F hMC y f) J (-(r : ℤ)) hJ hk =
      f.val.component J (-(r : ℤ)) hJ hk
  have hSubset := dgCoherentBarCoconeSubsetHom_heq R D F hMC y
    (dgCoherentBarCoconeInverseSimplex R D F hMC y f) J (-(r : ℤ)) hJ hk r hcJ
  unfold dgCoherentBarCoconeSubsetParameterHom at hSubset
  rw [← dgCoherentBarCoconeInverseSimplex_map, dgCoherentBarCoconeInverseSimplex_hom] at hSubset
  simp only [dgCoherentBarInverseFullHom, dgCoherentBarInverseParameterCoefficient,
    Int.negOnePow_neg, smul_smul, Int.units_mul_self, one_smul] at hSubset
  rw [DGNerve.PinchedHom.LinearSimplex.pullback_val,
    DGNerve.PinchedHom.LinearData.pullback_component_of_inj
      (J.orderEmbOfFin hcJ).toOrderHom f.val Finset.univ (-(r : ℤ))
      Finset.univ_nonempty (by simp) (J.orderEmbOfFin hcJ).injective.injOn] at hSubset
  have hImg : (Finset.univ : Finset (Fin (r + 1))).image (J.orderEmbOfFin hcJ).toOrderHom = J :=
    J.image_orderEmbOfFin_univ hcJ
  simpa only [hImg] using eq_of_heq hSubset

lemma dgCoherentBarCoconeHomSpaceInverse_comparison_app {n : ℕ}
    (f : (DGNerve.pinchedHom R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y)) _⦋n⦌) :
    (dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app (Opposite.op ⦋n⦌)
      ((dgCoherentBarCoconeHomSpaceInverse R D F hMC y).app (Opposite.op ⦋n⦌) f) = f := by
  apply (DGNerve.PinchedHom.linearEquiv (dgCoherentBarNormalizedModule R D F hMC)
    (dgNerve.vertexEquiv R (RightModule R D) y) n).injective
  apply Subtype.ext
  change DGNerve.PinchedHom.toLinearData
    ((dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app (Opposite.op ⦋n⦌)
      (dgCoherentBarCoconeInverseSimplex R D F hMC y (DGNerve.PinchedHom.toLinearSimplex f))) =
        DGNerve.PinchedHom.toLinearData f
  rw [dgCoherentBarCoconeHomSpaceComparison_linear]
  exact dgCoherentBarCoconeInverseSimplex_linear R D F hMC y (DGNerve.PinchedHom.toLinearSimplex f)

def dgCoherentBarCoconeHomSpaceIso : coconeMappingSpace F y ≅
    DGNerve.pinchedHom R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) where
  hom := dgCoherentBarCoconeHomSpaceComparison R D F hMC y
  inv := dgCoherentBarCoconeHomSpaceInverse R D F hMC y
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro c
    exact dgCoherentBarCoconeHomSpaceComparison_inverse_app R D F hMC y c
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro f
    exact dgCoherentBarCoconeHomSpaceInverse_comparison_app R D F hMC y f

abbrev dgCoherentBarCoconeHomSpaceIsoUnconditional : coconeMappingSpace F y ≅
    DGNerve.pinchedHom R (RightModule R D)
      (dgCoherentBarNormalizedModule R D F (dgCoherentBarTheta_maurerCartan R D F))
      (dgNerve.vertexEquiv R (RightModule R D) y) :=
  dgCoherentBarCoconeHomSpaceIso R D F (dgCoherentBarTheta_maurerCartan R D F) y

end SerrePositivity.InfinityCategories
