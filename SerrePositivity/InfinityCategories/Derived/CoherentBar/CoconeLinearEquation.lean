module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearFullEquation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearNaturality
public import SerrePositivity.InfinityCategories.DGNerve.PinchedLinearPullback
/-!
概要：回収した全 pinched 成分族が線形単体方程式を満たすことを示す。
方針：部分集合の昇順列挙へ制限し、既存の単射方程式移送を直接使う。
規約：全部分集合と任意の指定次数を扱う。
使われ方：余錐空間から実 pinched Hom への全単体比較。
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

lemma dgCoherentBarCoconeLinearData_mem {n : ℕ} (c : (coconeMappingSpace F y) _⦋n⦌) :
    dgCoherentBarCoconeLinearData R D F hMC y c ∈
      DGNerve.PinchedHom.linearSubmodule R (dgCoherentBarNormalizedModule R D F hMC)
        (dgNerve.vertexEquiv R (RightModule R D) y) n := by
  intro J k hJ hk
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hkr : k = -(r : ℤ) := by omega
  cases hkr
  let α := (J.orderEmbOfFin hc).toOrderHom
  have hi : Set.InjOn α ((Finset.univ : Finset (Fin (r + 1))) : Set _) :=
    (J.orderEmbOfFin hc).injective.injOn
  have him : (Finset.univ : Finset (Fin (r + 1))).image α = J :=
    J.image_orderEmbOfFin_univ hc
  have h := dgCoherentBarCoconeLinearData_full_equation R D F hMC y
    ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c)
  have hNat := dgCoherentBarCoconeLinearData_map R D F hMC y c α
  simp only [hNat] at h
  rw [DGNerve.PinchedHom.LinearData.pullback_component_of_inj α _ Finset.univ
      (-(r : ℤ)) Finset.univ_nonempty (by simp) hi,
    DGNerve.PinchedHom.LinearData.pullback_rhs_of_inj _ α Finset.univ (-(r : ℤ))
      (by simp) hi] at h
  simpa only [him] using h

def dgCoherentBarCoconeLinearSimplex {n : ℕ} (c : (coconeMappingSpace F y) _⦋n⦌) :
    DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) n :=
  ⟨dgCoherentBarCoconeLinearData R D F hMC y c, dgCoherentBarCoconeLinearData_mem R D F hMC y c⟩

lemma dgCoherentBarCoconeLinearSimplex_map {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarCoconeLinearSimplex R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) =
    DGNerve.PinchedHom.LinearSimplex.pullback α (dgCoherentBarCoconeLinearSimplex R D F hMC y c) :=
  Subtype.ext (dgCoherentBarCoconeLinearData_map R D F hMC y c α)

end SerrePositivity.InfinityCategories
