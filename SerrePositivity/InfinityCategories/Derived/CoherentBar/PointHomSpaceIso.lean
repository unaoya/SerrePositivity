module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointFiberCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LeftRightTopCoordinates
/-!
概要：正規化 bar の一点図式の余錐空間を、実右 pinched Hom と厳密に同定する。
方針：coslice fiber と左 Hom の同型、端点正規化、明示左右同型を合成する。
規約：最上成分の実計算則を併設する。
使われ方：固定終点の回収写像の同値性と標準族の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarCosliceFiberSimplex_sourceObj (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (x y : (dgNerve R C) _⦋0⦌) {n : ℕ}
    (c : (coconeMappingSpace (SSet.yonedaEquiv.symm x) y) _⦋n⦌) :
    (cosliceFiberSimplex n c).obj 0 = dgNerve.vertexEquiv R C x :=
  congrArg (dgNerve.vertexEquiv R C) (cosliceFiberSimplex_source n c)

lemma dgCoherentBarCosliceFiberSimplex_targetObj (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (x y : (dgNerve R C) _⦋0⦌) {n : ℕ}
    (c : (coconeMappingSpace (SSet.yonedaEquiv.symm x) y) _⦋n⦌) :
    (cosliceFiberSimplex n c).obj (Fin.last (n + 1)) = dgNerve.vertexEquiv R C y := by
  have h := congrArg (fun t : Simplex R C n => t.obj (Fin.last n))
    (cosliceFiberSimplex_target n c)
  have he : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom (Fin.last n) =
      Fin.last (n + 1) := by
    apply Fin.ext
    change ((0 : Fin (n + 2)).succAbove (Fin.last n)).val = n + 1
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
    rfl
  change (cosliceFiberSimplex n c).obj
    ((SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom (Fin.last n)) = _ at h
  rwa [he] at h

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarPointHomSpaceIso :
    coconeMappingSpace ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)) y ≅
    DGNerve.pinchedHom R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) :=
  (pinchedLeftCosliceFiberIso (dgCoherentBarNativeApex R D F hMC) y).symm ≪≫
    eqToIso (congrArg₂ (fun a b => pinchedHomLeft (X := dgNerve R (RightModule R D)) a b)
      (rfl : dgCoherentBarNativeApex R D F hMC =
        Simplex.vertex (A := R) (dgCoherentBarNormalizedModule R D F hMC))
      ((dgNerve.vertexEquiv R (RightModule R D)).symm_apply_apply y).symm) ≪≫
    dgCoherentBarLeftRightHomIso R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y)

lemma dgCoherentBarPointHomSpaceIso_top {n : ℕ}
    (c : (coconeMappingSpace ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)) y) _⦋n⦌) :
    HEq (dgCoherentBarPinchedTop R (RightModule R D)
      (dgCoherentBarNormalizedModule R D F hMC) (dgNerve.vertexEquiv R (RightModule R D) y)
      ((dgCoherentBarPointHomSpaceIso R D F hMC y).hom.app (Opposite.op ⦋n⦌) c))
      ((n : ℤ).negOnePow • (cosliceFiberSimplex n c).hom Finset.univ 0 (Fin.last (n + 1))
        (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
        (coherentDiagramTop_max n) (by simp; omega)) := by
  let e := pinchedLeftCosliceFiberIso (dgCoherentBarNativeApex R D F hMC) y
  let l := e.inv.app (Opposite.op ⦋n⦌) c
  let hy := ((dgNerve.vertexEquiv R (RightModule R D)).symm_apply_apply y).symm
  let l' := (eqToHom (congrArg₂ (fun a b => pinchedHomLeft
    (X := dgNerve R (RightModule R D)) a b) rfl hy)).app (Opposite.op ⦋n⦌) l
  have hTop := dgCoherentBarLeftRightHomIso_top R (RightModule R D)
    (dgCoherentBarNormalizedModule R D F hMC) (dgNerve.vertexEquiv R (RightModule R D) y) l'
  have hVal : pinchedLeftSimplexVal n l' = cosliceFiberSimplex n c := by
    dsimp only [l']
    rw [pinchedHomLeft_eqToHom_app_val rfl hy]
    have h := dgLeftPinchedCosliceFiberIso_simplex (dgCoherentBarNativeApex R D F hMC) y l
    have hInv := ConcreteCategory.congr_hom (Iso.inv_hom_id_app e (Opposite.op ⦋n⦌)) c
    change e.hom.app (Opposite.op ⦋n⦌) (e.inv.app (Opposite.op ⦋n⦌) c) = c at hInv
    change cosliceFiberSimplex n (e.hom.app (Opposite.op ⦋n⦌)
      (e.inv.app (Opposite.op ⦋n⦌) c)) = pinchedLeftSimplexVal n l at h
    rw [hInv] at h
    exact h.symm
  rw [hVal] at hTop
  exact hTop

end SerrePositivity.InfinityCategories
