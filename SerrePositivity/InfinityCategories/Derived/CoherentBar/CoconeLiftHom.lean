module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeHomUniversalColumns
/-!
概要：持ち上げ余錐の最上混合成分から、正規化実 bar の斉次 Hom を回収する。
方針：非退化成分の族を native Hom 線形同値の逆に入れ、最終頂点を終域にする。
規約：m パラメーターに次数 −m を対応させ、微分方程式をまだ仮定しない。
使われ方：標準 Hom の持ち上げの高次補正と、その一意性。
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

def dgCoherentBarCoconeLiftHom {m : ℕ} (c : (sliceUnder F) _⦋m⦌) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeLiftTarget R D F c)).X (-(m : ℤ)) :=
  (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgCoherentBarCoconeLiftTarget R D F c) (-(m : ℤ))).symm
    (fun s => dgCoherentBarCoconeLiftColumn R D F c s.val)

lemma dgCoherentBarCoconeLiftHom_nondegenerate {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : dgCoherentBarNormalizedIndex I) :
    compose R (x := dgCoherentBarSource R D F s.val)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgCoherentBarCoconeLiftTarget R D F c)
      (dgCoherentBarCoconeLiftHom R D F hMC c)
      (dgCoherentBarNativeColumn R D F hMC s.val)
      (show -(s.val.1 : ℤ) + -(m : ℤ) = -(m : ℤ) - (s.val.1 : ℤ) by omega) =
      dgCoherentBarCoconeLiftColumn R D F c s.val := by
  rw [dgCoherentBarNativeColumn_compose_eq_coordinates, dgCoherentBarCoconeLiftHom,
    LinearEquiv.apply_symm_apply]

lemma dgCoherentBarCoconeLiftHom_unique {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌)
    (z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeLiftTarget R D F c)).X (-(m : ℤ)))
    (hz : ∀ s : dgCoherentBarNormalizedIndex I,
      compose R (x := dgCoherentBarSource R D F s.val)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgCoherentBarCoconeLiftTarget R D F c) z
        (dgCoherentBarNativeColumn R D F hMC s.val)
        (show -(s.val.1 : ℤ) + -(m : ℤ) = -(m : ℤ) - (s.val.1 : ℤ) by omega) =
        dgCoherentBarCoconeLiftColumn R D F c s.val) :
    z = dgCoherentBarCoconeLiftHom R D F hMC c := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgCoherentBarCoconeLiftTarget R D F c) (-(m : ℤ))).injective
  funext s
  rw [← dgCoherentBarNativeColumn_compose_eq_coordinates, hz,
    dgCoherentBarCoconeLiftHom, LinearEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
