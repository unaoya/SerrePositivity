module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PointHomSpaceIso
/-!
概要：各固定終点での一点下への回収写像は、既存の右 Hom 同型と厳密に整合する同型である。
方針：全次数の最上成分を左右 Hom の次数符号で照合し、単体写像の外延性を使う。
規約：ホモトピー群だけでなく実単体写像の等号を証明する。
使われ方：指定 native 余錐の標準 Hom の族の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeHomSpaceComparison_top {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) :
    HEq (dgCoherentBarPinchedTop R (RightModule R D)
      (dgCoherentBarNormalizedModule R D F hMC) (dgNerve.vertexEquiv R (RightModule R D) y)
      ((dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app (Opposite.op ⦋n⦌) c))
      ((n : ℤ).negOnePow • dgCoherentBarCoconeFamilyHom R D F hMC y c) := by
  unfold dgCoherentBarPinchedTop
  rw [dgCoherentBarCoconeHomSpaceComparison_linear]
  have h := dgCoherentBarCoconeSubsetHom_heq R D F hMC y c Finset.univ (-(n : ℤ))
    Finset.univ_nonempty (by simp) n (by simp)
  unfold dgCoherentBarCoconeSubsetParameterHom at h
  rw [dgCoherentBarUniv_orderHom, op_id, CategoryTheory.Functor.map_id_apply] at h
  exact h

lemma dgCoherentBarCoconePointFiber_comparison :
    dgCoherentBarCoconePointFiber R D F hMC y ≫ (dgCoherentBarPointHomSpaceIso R D F hMC y).hom =
      dgCoherentBarCoconeHomSpaceComparison R D F hMC y := by
  apply dgCoherentBarPinched_hom_ext_of_top R (RightModule R D)
    (dgCoherentBarNormalizedModule R D F hMC) (dgNerve.vertexEquiv R (RightModule R D) y)
  intro n c
  let c' := (dgCoherentBarCoconePointFiber R D F hMC y).app (Opposite.op ⦋n⦌) c
  have hPoint := dgCoherentBarPointHomSpaceIso_top R D F hMC y c'
  have hFull := dgCoherentBarCoconePointFiber_full_hom_heq R D F hMC y c
  have hx := dgCoherentBarCosliceFiberSimplex_sourceObj R (RightModule R D)
    (dgCoherentBarNativeApex R D F hMC) y c'
  have hz := dgCoherentBarCosliceFiberSimplex_targetObj R (RightModule R D)
    (dgCoherentBarNativeApex R D F hMC) y c'
  have hScalar := dgCoherentBarHom_units_smul_heq (R := R) (C := RightModule R D)
    hx hz rfl (n : ℤ).negOnePow _ _ hFull
  exact eq_of_heq (hPoint.trans (hScalar.trans
    (dgCoherentBarCoconeHomSpaceComparison_top R D F hMC y c).symm))

def dgCoherentBarCoconePointFiberIso : coconeMappingSpace F y ≅
    coconeMappingSpace ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)) y :=
  dgCoherentBarCoconeHomSpaceIso R D F hMC y ≪≫ (dgCoherentBarPointHomSpaceIso R D F hMC y).symm

lemma dgCoherentBarCoconePointFiberIso_hom :
    (dgCoherentBarCoconePointFiberIso R D F hMC y).hom =
      dgCoherentBarCoconePointFiber R D F hMC y := by
  apply (cancel_mono (dgCoherentBarPointHomSpaceIso R D F hMC y).hom).1
  simp only [dgCoherentBarCoconePointFiberIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (dgCoherentBarCoconePointFiber_comparison R D F hMC y).symm

lemma dgCoherentBarCoconePointFiber_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (dgCoherentBarCoconePointFiber R D F hMC y) := by
  rw [← dgCoherentBarCoconePointFiberIso_hom]
  exact (qCatEquivalenceOfIso (dgCoherentBarCoconePointFiberIso R D F hMC y)).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
