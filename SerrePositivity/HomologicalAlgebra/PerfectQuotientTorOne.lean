module

public import SerrePositivity.HomologicalAlgebra.QuotientTorOneConormal
public import SerrePositivity.CommutativeAlgebra.PerfectRadicalIdeal

/-! # First self-Tor of a radical quotient of a perfect characteristic-p ring

This is a degree-one quotient case, not the full Tor-independence theorem for
arbitrary diagrams of perfect rings.
-/

@[expose] public section
universe u
namespace SerrePositivity
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
  [CharP R p] [PerfectRing R p] (I : Ideal R)

include p in
lemma radicalIdeal_quotientTorOne_subsingleton (hI : I.IsRadical) :
    Subsingleton (TorModule R 1 (R ⧸ I) (R ⧸ I)) :=
  (quotientTorOne_subsingleton_iff_idempotent R I).mpr
    (radicalIdeal_idempotent_of_perfectRing R I p hI)

end SerrePositivity
