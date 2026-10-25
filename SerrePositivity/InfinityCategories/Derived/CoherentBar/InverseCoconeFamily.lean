module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseOverSection
/-!
概要：任意の pinched 線形単体を、終点固定の実余錐族へ逆構成する。
方針：slice への射を既存の普遍性で uncurry し、左右の制限を検証する。
規約：元の coherent 図式を厳密に保ち、正規化加群の型を変更しない。
使われ方：全余錐空間と実 Hom の比較の逆射。
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

def dgCoherentBarCoconeInverseSimplex {m : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) m) :
    (coconeMappingSpace F y) _⦋m⦌ := by
  refine ⟨⟨sliceOverUncurry (dgCoherentBarInverseOverSection R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) f), ?_⟩, ?_⟩
  · rw [sliceOverUncurry_projection, dgCoherentBarInverseOverSection_projection]
  · change SSet.yonedaEquiv (joinInr _ Δ[m] ≫
      sliceOverUncurry (dgCoherentBarInverseOverSection R D F hMC
        (dgNerve.vertexEquiv R (RightModule R D) y) f)) =
      InfinityCategories.PinchedHom.constant y m
    rw [sliceOverUncurry_fixed, Equiv.apply_symm_apply]
    exact congrArg (fun z : (dgNerve R (RightModule R D)) _⦋0⦌ =>
      InfinityCategories.PinchedHom.constant z m)
      ((dgNerve.vertexEquiv R (RightModule R D)).symm_apply_apply y)

lemma dgCoherentBarCoconeInverseSimplex_family {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) m) (s : I _⦋n⦌) :
    dgCoherentBarCoconeFamilySimplex R D F y
      (dgCoherentBarCoconeInverseSimplex R D F hMC y f) s =
    dgCoherentBarInverseSimplex R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y) f s := by
  let sectionMap := dgCoherentBarInverseOverSection R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) f
  have hCurry := sliceOverCurry_uncurry sectionMap
  have hCell := congrArg (fun g =>
    (g.app (Opposite.op ⦋n⦌) (ULift.up s)).val) hCurry
  change joinMap ((SSet.yonedaEquiv
      (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm (ULift.up s))
      (𝟙 Δ[m]) ≫ sliceOverUncurry sectionMap =
    (joinStdSimplexIso n m).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarInverseSimplex R D F hMC
          (dgNerve.vertexEquiv R (RightModule R D) y) f s) at hCell
  change SSet.yonedaEquiv ((joinStdSimplexIso n m).inv ≫
    (joinMap ((SSet.yonedaEquiv
      (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm (ULift.up s))
      (𝟙 Δ[m]) ≫ sliceOverUncurry sectionMap)) = _
  rw [hCell, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
