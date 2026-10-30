module

public import SerrePositivity.PerfectComplex.InvolutionDecomposition
public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentQuasiIso

/-! # Restriction of equivariant maps to involution eigenspaces -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma positive_naturality (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) :
    t.positive.map ≫ f = f ≫ s.positive.map := by
  change ((⅟(2 : R)) • (𝟙 K + t.map)) ≫ f = f ≫ ((⅟(2 : R)) • (𝟙 L + s.map))
  simp [add_comp, comp_add, hf]

lemma negative_naturality (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) :
    t.negative.map ≫ f = f ≫ s.negative.map := by
  change (𝟙 K - t.positive.map) ≫ f = f ≫ (𝟙 L - s.positive.map)
  rw [sub_comp, comp_sub, id_comp, comp_id, positive_naturality t s f hf]

abbrev positiveImageMap (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) : t.positive.image ⟶ s.positive.image :=
  CochainIdempotent.imageMap t.positive s.positive f (positive_naturality t s f hf)

abbrev negativeImageMap (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) : t.negative.image ⟶ s.negative.image :=
  CochainIdempotent.imageMap t.negative s.negative f (negative_naturality t s f hf)

lemma positiveImageMap_quasiIso (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) [QuasiIso f] :
    QuasiIso (positiveImageMap t s f hf) :=
  CochainIdempotent.imageMap_quasiIso _ _ _ _

lemma negativeImageMap_quasiIso (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) [QuasiIso f] :
    QuasiIso (negativeImageMap t s f hf) :=
  CochainIdempotent.imageMap_quasiIso _ _ _ _

end CochainInvolution
end SerrePositivity
