module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Order.SuccPred.Nat

/-! # The actual simplex category and its opposite as Reedy categories

Inverse maps are epimorphisms, direct maps are monomorphisms. The unique
factorization uses Mathlib's existing strong epi/mono image factorization.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open MorphismProperty

namespace SerrePositivity.Reedy

abbrev simplexInverse := epimorphisms SimplexCategory
abbrev simplexDirect := monomorphisms SimplexCategory

lemma simplex_inverse_degree_lt {i j : SimplexCategory} (f : i ⟶ j)
    (hf : simplexInverse f) (hf' : ¬identities SimplexCategory f) : j.len < i.len := by
  have : Epi f := hf
  apply lt_of_le_of_ne (SimplexCategory.len_le_of_epi f)
  intro h
  have hij : i = j := SimplexCategory.ext h.symm
  subst j
  apply hf'
  rw [SimplexCategory.eq_id_of_epi f]
  exact ofHoms.mk i

lemma simplex_direct_degree_lt {i j : SimplexCategory} (f : i ⟶ j)
    (hf : simplexDirect f) (hf' : ¬identities SimplexCategory f) : i.len < j.len := by
  have : Mono f := hf
  apply lt_of_le_of_ne (SimplexCategory.len_le_of_mono f)
  intro h
  have hij : i = j := SimplexCategory.ext h
  subst j
  apply hf'
  rw [SimplexCategory.eq_id_of_mono f]
  exact ofHoms.mk i

def simplexFactorization {i j : SimplexCategory} (f : i ⟶ j) :
    MapFactorizationData simplexInverse simplexDirect f where
  Z := image f
  i := factorThruImage f
  p := image.ι f
  fac := image.fac f
  hi := inferInstanceAs (Epi (factorThruImage f))
  hp := inferInstanceAs (Mono (image.ι f))

lemma simplexFactorization_unique {i j : SimplexCategory} (f : i ⟶ j)
    (d : MapFactorizationData simplexInverse simplexDirect f) : d = simplexFactorization f := by
  rcases d with ⟨Z, a, b, hab, ha, hb⟩
  have : Epi a := ha
  have : Mono b := hb
  have hZ : image f = Z := SimplexCategory.image_eq hab
  subst Z
  have hb' : image.ι f = b := SimplexCategory.image_ι_eq hab
  have ha' : factorThruImage f = a := SimplexCategory.factorThruImage_eq hab
  subst a
  subst b
  rfl

def simplex : ReedyStructure simplexInverse simplexDirect ℕ where
  deg := SimplexCategory.len
  lt₁ := simplex_inverse_degree_lt
  lt₂ := simplex_direct_degree_lt
  nonempty_unique f := ⟨{
    default := simplexFactorization f
    uniq := simplexFactorization_unique f }⟩

abbrev simplexOp : ReedyStructure simplexDirect.op simplexInverse.op ℕ := simplex.op

end SerrePositivity.Reedy

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.9.5"] _root_.SerrePositivity.Reedy.simplex
attribute [cite HTT "A.2.9.5"] _root_.SerrePositivity.Reedy.simplexDirect
attribute [cite HTT "A.2.9.5"] _root_.SerrePositivity.Reedy.simplexInverse
