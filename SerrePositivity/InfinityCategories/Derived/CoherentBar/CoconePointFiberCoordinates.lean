module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointComparisonIdentity
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PinchedTopCoordinates
/-!
概要：終点固定の回収写像の元の左 Hom 単体と最上 Hom 成分を計算する。
方針：一点 join の次元正規化を明示し、全頂点成分は次元の等号を越えて保持する。
規約：対象・次数を異種等号で保ち、固定終点の全次数を扱う。
使われ方：回収写像と既存の右 pinched Hom 同型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarCastFullHom_heq {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] {m n : ℕ} (h : m = n) (s : Simplex R C (m + 1)) :
    HEq ((SSet.yonedaEquiv ((simplexCastIso (congrArg Nat.succ h)).inv ≫
      (SSet.yonedaEquiv (X := dgNerve R C)).symm s)).hom Finset.univ
      0 (Fin.last (n + 1)) (-(n : ℤ)) (coherentDiagramTop_card n)
      (coherentDiagramTop_min n) (coherentDiagramTop_max n) (by simp; omega))
      (s.hom Finset.univ 0 (Fin.last (m + 1)) (-(m : ℤ))
        (coherentDiagramTop_card m) (coherentDiagramTop_min m)
        (coherentDiagramTop_max m) (by simp; omega)) := by
  subst n
  have hId : (𝟙 ⦋m + 1⦌) = SimplexCategory.Hom.mk
      (OrderHom.id : Fin (m + 2) →o Fin (m + 2)) := by
    ext i
    rfl
  have hSimplex : SSet.yonedaEquiv ((simplexCastIso (congrArg Nat.succ (rfl : m = m))).inv ≫
      (SSet.yonedaEquiv (X := dgNerve R C)).symm s) = s := by
    change SSet.yonedaEquiv (SSet.stdSimplex.map (𝟙 ⦋m + 1⦌) ≫
      (SSet.yonedaEquiv (X := dgNerve R C)).symm s) = s
    rw [hId, SSet.stdSimplex.map_id, Category.id_comp, Equiv.apply_symm_apply]
  exact Simplex.hom_heq_of_eq hSimplex Finset.univ 0 (Fin.last (m + 1)) (-(m : ℤ))
    (coherentDiagramTop_card m) (coherentDiagramTop_min m)
    (coherentDiagramTop_max m) (by simp; omega)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarCoconePointFiber : coconeMappingSpace F y ⟶
    coconeMappingSpace ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)) y :=
  vertexFiberMap (sliceUnderProjection F) (sliceUnderProjection
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)))
    (dgCoherentBarCoconePointComparison R D F hMC)
    (dgCoherentBarCoconePointComparison_projection R D F hMC) y

lemma dgCoherentBarCoconePointFiber_cosliceSimplex {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) :
    cosliceFiberSimplex n ((dgCoherentBarCoconePointFiber R D F hMC y).app (Opposite.op ⦋n⦌) c) =
      SSet.yonedaEquiv ((simplexCastIso (show 0 + n + 1 = n + 1 by omega)).inv ≫
        (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
          (dgCoherentBarCoconeRecoveredSimplex R D F hMC c.val)) := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    ((joinStdSimplexIso 0 n).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarCoconeRecoveredSimplex R D F hMC c.val))) = _
  simp only [leftPointStdSimplexIso, pointJoinStdSimplexIso, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id_assoc]

lemma dgCoherentBarCoconePointFiber_full_hom_heq {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) :
    HEq ((cosliceFiberSimplex n
      ((dgCoherentBarCoconePointFiber R D F hMC y).app (Opposite.op ⦋n⦌) c)).hom
      Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ)) (coherentDiagramTop_card n)
      (coherentDiagramTop_min n) (coherentDiagramTop_max n) (by simp; omega))
      (dgCoherentBarCoconeFamilyHom R D F hMC y c) := by
  rw [dgCoherentBarCoconePointFiber_cosliceSimplex]
  have hCast := dgCoherentBarCastFullHom_heq (R := R) (C := RightModule R D)
    (m := 0 + n) (n := n) (by omega) (dgCoherentBarCoconeRecoveredSimplex R D F hMC c.val)
  have hDegree : HEq
      ((dgCoherentBarCoconeRecoveredSimplex R D F hMC c.val).hom Finset.univ
        0 (Fin.last (0 + n + 1)) (-((0 + n : ℕ) : ℤ))
        (coherentDiagramTop_card (0 + n)) (coherentDiagramTop_min (0 + n))
        (coherentDiagramTop_max (0 + n)) (by simp; omega))
      ((dgCoherentBarCoconeRecoveredSimplex R D F hMC c.val).hom Finset.univ
        0 (Fin.last (0 + n + 1)) (-(n : ℤ))
        (coherentDiagramTop_card (0 + n)) (coherentDiagramTop_min (0 + n))
        (coherentDiagramTop_max (0 + n)) (by simp; omega)) :=
    SimplexData.hom_heq_of_indices_degree _ rfl rfl rfl (by omega)
  exact hCast.trans (hDegree.trans
    ((dgCoherentBarCoconeRecoveredRawData_full_hom_heq R D F hMC c.val).trans
      (dgCoherentBarCoconeLiftHom_fixed R D F hMC y c)))

end SerrePositivity.InfinityCategories
