module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeHomUniversalColumns
/-!
概要：任意次数の余錐族の最上混合成分から、正規化実 bar の斉次 Hom を回収する。
方針：非退化成分の族を全次数の native Hom 線形同値の逆に入れる。
規約：m パラメーターに次数 −m を対応させ、微分方程式をまだ仮定しない。
使われ方：写像空間の逆構成の高次成分と、その成分による一意性。
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

def dgCoherentBarCoconeFamilyHom {m : ℕ} (c : (coconeMappingSpace F y) _⦋m⦌) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y)).X (-(m : ℤ)) :=
  (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) (-(m : ℤ))).symm
    (fun s => dgCoherentBarCoconeFamilyColumn R D F y c s.val)

lemma dgCoherentBarCoconeFamilyHom_nondegenerate {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : dgCoherentBarNormalizedIndex I) :
    compose R (x := dgCoherentBarSource R D F s.val)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarCoconeFamilyHom R D F hMC y c)
      (dgCoherentBarNativeColumn R D F hMC s.val)
      (show -(s.val.1 : ℤ) + -(m : ℤ) = -(m : ℤ) - (s.val.1 : ℤ) by omega) =
      dgCoherentBarCoconeFamilyColumn R D F y c s.val := by
  rw [dgCoherentBarNativeColumn_compose_eq_coordinates, dgCoherentBarCoconeFamilyHom,
    LinearEquiv.apply_symm_apply]

lemma dgCoherentBarCoconeFamilyHom_unique {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌)
    (z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y)).X (-(m : ℤ)))
    (hz : ∀ s : dgCoherentBarNormalizedIndex I,
      compose R (x := dgCoherentBarSource R D F s.val)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgNerve.vertexEquiv R (RightModule R D) y) z
        (dgCoherentBarNativeColumn R D F hMC s.val)
        (show -(s.val.1 : ℤ) + -(m : ℤ) = -(m : ℤ) - (s.val.1 : ℤ) by omega) =
        dgCoherentBarCoconeFamilyColumn R D F y c s.val) :
    z = dgCoherentBarCoconeFamilyHom R D F hMC y c := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) (-(m : ℤ))).injective
  funext s
  rw [← dgCoherentBarNativeColumn_compose_eq_coordinates, hz,
    dgCoherentBarCoconeFamilyHom, LinearEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
