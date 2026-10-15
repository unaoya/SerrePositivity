module
public import SerrePositivity.HomologicalAlgebra.CochainLinearDual

/-! # Homology of nonnegative restrictions, including the degree-zero boundary -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Restriction to nonnegative degrees preserves cycles in every natural degree. -/
abbrev nonnegativeCochainCyclesIso (K : CochainComplex C ℤ) (n : ℕ) :
    (K.restriction nonnegativeCochainEmbedding).cycles n ≅ K.cycles (n : ℤ) :=
  K.restrictionCyclesIso nonnegativeCochainEmbedding (j := n) (k := n + 1)
    (hk := by simp [CochainComplex.next]) (j' := (n : ℤ)) (k' := ((n + 1 : ℕ) : ℤ))
    (hj' := rfl) (hk' := rfl) (hk'' := by simp [CochainComplex.next])

/-- At degree zero, vanishing negative terms makes cycles equal to full homology. -/
def nonnegativeCochainHomologyIsoZero (K : CochainComplex C ℤ)
    (hK : ∀ q : ℤ, q < 0 → IsZero (K.X q)) :
    (K.restriction nonnegativeCochainEmbedding).homology 0 ≅ K.homology 0 :=
  haveI : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0
    (by simp [CochainComplex.prev]) ((hK (-1) (by omega)).eq_of_src _ _)
  (asIso ((K.restriction nonnegativeCochainEmbedding).homologyπ 0)).symm ≪≫
    nonnegativeCochainCyclesIso K 0 ≪≫ asIso (K.homologyπ 0)

/-- At positive natural degrees the restriction has both adjacent terms. -/
def nonnegativeCochainHomologyIsoSucc (K : CochainComplex C ℤ) (n : ℕ) :
    (K.restriction nonnegativeCochainEmbedding).homology (n + 1) ≅
      K.homology ((n + 1 : ℕ) : ℤ) :=
  K.restrictionHomologyIso nonnegativeCochainEmbedding n (n + 1) (n + 2)
    (by simp) (by simp [CochainComplex.next])
    (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) (k' := ((n + 2 : ℕ) : ℤ))
    rfl rfl rfl (by simp [CochainComplex.prev]) (by simp [CochainComplex.next]; omega)

/-- Nonnegative restriction preserves every natural homology degree of a nonnegative complex. -/
def nonnegativeCochainHomologyIso (K : CochainComplex C ℤ)
    (hK : ∀ q : ℤ, q < 0 → IsZero (K.X q)) :
    ∀ n : ℕ, (K.restriction nonnegativeCochainEmbedding).homology n ≅ K.homology (n : ℤ)
  | 0 => nonnegativeCochainHomologyIsoZero K hK
  | n + 1 => nonnegativeCochainHomologyIsoSucc K n

/-- The comparison intertwines the canonical quotient maps out of cycles. -/
@[reassoc] lemma nonnegativeCochainHomologyIso_homologyπ (K : CochainComplex C ℤ)
    (hK : ∀ q : ℤ, q < 0 → IsZero (K.X q)) (n : ℕ) :
    (K.restriction nonnegativeCochainEmbedding).homologyπ n ≫
        (nonnegativeCochainHomologyIso K hK n).hom =
      (nonnegativeCochainCyclesIso K n).hom ≫ K.homologyπ (n : ℤ) := by
  cases n with
  | zero =>
    have : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0
      (by simp [CochainComplex.prev]) ((hK (-1) (by omega)).eq_of_src _ _)
    simp [nonnegativeCochainHomologyIso, nonnegativeCochainHomologyIsoZero]
  | succ n => exact homologyπ_restrictionHomologyIso_hom ..

/-- Restriction of cycles is natural for arbitrary cochain maps. -/
@[reassoc] lemma nonnegativeCochainCyclesIso_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℕ) :
    cyclesMap (restrictionMap f nonnegativeCochainEmbedding) n ≫
        (nonnegativeCochainCyclesIso L n).hom =
      (nonnegativeCochainCyclesIso K n).hom ≫ cyclesMap f (n : ℤ) := by
  apply (cancel_mono (L.iCycles (n : ℤ))).mp
  simp only [Category.assoc, nonnegativeCochainCyclesIso,
    restrictionCyclesIso_hom_iCycles, cyclesMap_i_assoc,
    restrictionCyclesIso_hom_iCycles_assoc, cyclesMap_i]
  rw [restrictionMap_f' f nonnegativeCochainEmbedding rfl]
  simp [restrictionXIso, nonnegativeCochainEmbedding]

/-- All cochain maps between nonnegative complexes commute with the homology comparison. -/
@[reassoc] lemma nonnegativeCochainHomologyIso_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : ∀ q : ℤ, q < 0 → IsZero (K.X q))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) (n : ℕ) :
    homologyMap (restrictionMap f nonnegativeCochainEmbedding) n ≫
        (nonnegativeCochainHomologyIso L hL n).hom =
      (nonnegativeCochainHomologyIso K hK n).hom ≫ homologyMap f (n : ℤ) := by
  apply (cancel_epi ((K.restriction nonnegativeCochainEmbedding).homologyπ n)).mp
  calc
    _ = cyclesMap (restrictionMap f nonnegativeCochainEmbedding) n ≫
        (L.restriction nonnegativeCochainEmbedding).homologyπ n ≫
          (nonnegativeCochainHomologyIso L hL n).hom := by
      rw [← Category.assoc, homologyπ_naturality, Category.assoc]
    _ = cyclesMap (restrictionMap f nonnegativeCochainEmbedding) n ≫
        (nonnegativeCochainCyclesIso L n).hom ≫ L.homologyπ (n : ℤ) := by
      rw [nonnegativeCochainHomologyIso_homologyπ]
    _ = (nonnegativeCochainCyclesIso K n).hom ≫ cyclesMap f (n : ℤ) ≫
        L.homologyπ (n : ℤ) := by
      rw [← Category.assoc, nonnegativeCochainCyclesIso_hom_naturality, Category.assoc]
    _ = (nonnegativeCochainCyclesIso K n).hom ≫ K.homologyπ (n : ℤ) ≫
        homologyMap f (n : ℤ) := by rw [homologyπ_naturality]
    _ = _ := by rw [← Category.assoc, ← nonnegativeCochainHomologyIso_homologyπ, Category.assoc]

end SerrePositivity
