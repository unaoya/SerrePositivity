module
public import SerrePositivity.HomologicalAlgebra.IdealPowerTorsion

/-! # Radical independence of the actual ideal-power torsion functor -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- Containment of an ideal power reverses containment of power-torsion submodules. -/
lemma primaryComponent_le_of_pow_le (I J : Ideal R) (k : ℕ) (hk : I ^ k ≤ J)
    (M : ModuleCat.{u} R) : J.primaryComponent M ≤ I.primaryComponent M := by
  intro x hx
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M J x).mp hx
  have hpow : I ^ (k * n) ≤ J ^ n := by
    rw [pow_mul]
    exact pow_le_pow_left' hk n
  apply (Ideal.primaryComponent_mem M I x).mpr
  refine ⟨k * n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff] at hn ⊢
  intro a
  exact hn ⟨a, hpow a.property⟩

/-- For finitely generated ideals, power torsion depends only on the radical. -/
lemma primaryComponent_eq_of_radical_eq_of_fg (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    (h : I.radical = J.radical) (M : ModuleCat.{u} R) :
    I.primaryComponent M = J.primaryComponent M := by
  obtain ⟨a, ha⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (Ideal.le_radical.trans_eq h) hI
  obtain ⟨b, hb⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (Ideal.le_radical.trans_eq h.symm) hJ
  exact le_antisymm (primaryComponent_le_of_pow_le J I b hb M)
    (primaryComponent_le_of_pow_le I J a ha M)

/-- Radical independence is natural for all coefficient morphisms, by the identity on elements. -/
def idealPowerTorsionRadicalNatIso (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    (h : I.radical = J.radical) : idealPowerTorsionFunctor I ≅ idealPowerTorsionFunctor J where
  hom := idealPowerTorsionNatTransOfLE I J
    (fun M => (primaryComponent_eq_of_radical_eq_of_fg I J hI hJ h M).le)
  inv := idealPowerTorsionNatTransOfLE J I
    (fun M => (primaryComponent_eq_of_radical_eq_of_fg I J hI hJ h M).ge)
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply (cancel_mono ((idealPowerTorsionInclusion I).app M)).mp
    simp only [NatTrans.comp_app, Category.assoc,
      idealPowerTorsionNatTransOfLE_inclusion, NatTrans.id_app, Category.id_comp]
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply (cancel_mono ((idealPowerTorsionInclusion J).app M)).mp
    simp only [NatTrans.comp_app, Category.assoc,
      idealPowerTorsionNatTransOfLE_inclusion, NatTrans.id_app, Category.id_comp]

end SerrePositivity
