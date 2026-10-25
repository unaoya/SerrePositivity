module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearData
public import SerrePositivity.InfinityCategories.DGNerve.PinchedLinearReindex
/-!
概要：回収した右 pinched 成分族は、全パラメーター写像による引き戻しに自然である。
方針：部分集合上の単射分岐ではラベルの等式、非単射分岐では退化消滅を使う。
規約：線形方程式の成立を先取りせず、成分族の段階で自然性を証明する。
使われ方：写像空間の逆比較を全ての面・退化と可換な射にする。
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

lemma dgCoherentBarCoconeSubsetHom_map_of_injOn {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    dgCoherentBarCoconeSubsetHom R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk =
    dgCoherentBarCoconeSubsetHom R D F hMC y c (J.image α) k (hJ.image α)
      (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hcI : (J.image α).card = r + 1 := by rw [Finset.card_image_of_injOn hi]; exact hc
  have hLabel := dgCoherentBarSubsetLabel_map_of_injOn c α J hi r hc
  have hPhi : HEq (dgCoherentBarCoconeSubsetParameterHom R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J r hc)
      (dgCoherentBarCoconeSubsetParameterHom R D F hMC y c (J.image α) r hcI) :=
    dgCoherentBarCoconeFamilyHom_heq_of_index_eq R D F hMC y _ _ hLabel
  have hScalar := dgCoherentBarHom_units_smul_heq (R := R) (C := RightModule R D)
    rfl rfl rfl (r : ℤ).negOnePow _ _ hPhi
  exact eq_of_heq ((dgCoherentBarCoconeSubsetHom_heq R D F hMC y
    ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk r hc).trans
    (hScalar.trans (dgCoherentBarCoconeSubsetHom_heq R D F hMC y c (J.image α) k
      (hJ.image α) (by rw [Finset.card_image_of_injOn hi]; exact hk) r hcI).symm))

lemma dgCoherentBarCoconeSubsetHom_map_of_not_injOn {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬Set.InjOn α (J : Set (Fin (m + 1)))) :
    dgCoherentBarCoconeSubsetHom R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk = 0 := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hDeg := dgCoherentBarSubsetLabel_degenerate_of_not_injOn c α J hi r hc
  have hPhi : dgCoherentBarCoconeSubsetParameterHom R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J r hc = 0 :=
    dgCoherentBarCoconeFamilyHom_degenerate R D F hMC y
      ⟨dgCoherentBarSubsetLabel
        ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J r hc, hDeg⟩
  unfold dgCoherentBarCoconeSubsetHom
  rw [hPhi, smul_zero]
  exact dgCoherentBarGradedTransport_zero R D rfl rfl _

lemma dgCoherentBarCoconeLinearData_map {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarCoconeLinearData R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) =
    DGNerve.PinchedHom.LinearData.pullback α (dgCoherentBarCoconeLinearData R D F hMC y c) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change dgCoherentBarCoconeSubsetHom R D F hMC y
    ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk =
    (DGNerve.PinchedHom.LinearData.pullback α
      (dgCoherentBarCoconeLinearData R D F hMC y c)).component J k hJ hk
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · rw [DGNerve.PinchedHom.LinearData.pullback_component_of_inj α _ J k hJ hk hi]
    exact dgCoherentBarCoconeSubsetHom_map_of_injOn R D F hMC y c α J k hJ hk hi
  · rw [DGNerve.PinchedHom.LinearData.pullback_component_of_not_inj α _ J k hJ hk hi]
    exact dgCoherentBarCoconeSubsetHom_map_of_not_injOn R D F hMC y c α J k hJ hk hi

end SerrePositivity.InfinityCategories
