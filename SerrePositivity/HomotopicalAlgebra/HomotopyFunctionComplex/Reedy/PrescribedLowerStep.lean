module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerNaturality
public import Mathlib.Order.SuccPred.Nat

/-! # Assemble independently prescribed new-degree cells into a natural lower system

Only incoming direct and outgoing inverse compatibility with the old
system is required. Unique Reedy factorization supplies naturality on all
other arrows, including arrows between distinct objects of the new degree.
No lifting, model structure or boundary limits are assumed here.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.PrescribedLowerStep
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  (F G : J ⥤ C) (n : ℕ) (old : lowerInclusion r n ⋙ F ⟶ lowerInclusion r n ⋙ G)

structure Data where
  hom (j : J) (hj : r.deg j = n) : F.obj j ⟶ G.obj j
  incoming (j : J) (hj : r.deg j = n) {x : Lower r n} (f : x.obj ⟶ j) (hf : direct f) :
    F.map f ≫ hom j hj = old.app x ≫ G.map f
  outgoing (j : J) (hj : r.deg j = n) {x : Lower r n} (f : j ⟶ x.obj) (hf : inverse f) :
    F.map f ≫ old.app x = hom j hj ≫ G.map f

namespace Data
variable {r F G n old} (d : Data r F G n old)

abbrev app (j : Lower r (n + 1)) : F.obj j.obj ⟶ G.obj j.obj :=
  if hj : r.deg j.obj < n then old.app ⟨j.obj, hj⟩
  else d.hom j.obj (le_antisymm (Nat.le_of_lt_succ j.property) (Nat.le_of_not_gt hj))

lemma naturality_direct {x y : Lower r (n + 1)} (f : x ⟶ y) (hf : direct f.hom) :
    F.map f.hom ≫ d.app y = d.app x ≫ G.map f.hom := by
  by_cases hy : r.deg y.obj < n
  · have hx := lt_of_le_of_lt (r.le₂ f.hom hf) hy
    rw [app, dite_eq_left hy, app, dite_eq_left hx]
    exact old.naturality (ObjectProperty.homMk f.hom : ⟨x.obj, hx⟩ ⟶ ⟨y.obj, hy⟩)
  · by_cases hid : MorphismProperty.identities J f.hom
    · exact naturality_on_lower_identities r (n + 1) d.app f hid
    · have hx := lt_of_lt_of_le (r.lt₂ f.hom hf hid) (Nat.le_of_lt_succ y.property)
      rw [app, dite_eq_right hy, app, dite_eq_left hx]
      exact d.incoming y.obj _ (x := ⟨x.obj, hx⟩) f.hom hf

lemma naturality_inverse {x y : Lower r (n + 1)} (f : x ⟶ y) (hf : inverse f.hom) :
    F.map f.hom ≫ d.app y = d.app x ≫ G.map f.hom := by
  by_cases hx : r.deg x.obj < n
  · have hy := lt_of_le_of_lt (r.le₁ f.hom hf) hx
    rw [app, dite_eq_left hy, app, dite_eq_left hx]
    exact old.naturality (ObjectProperty.homMk f.hom : ⟨x.obj, hx⟩ ⟶ ⟨y.obj, hy⟩)
  · by_cases hid : MorphismProperty.identities J f.hom
    · exact naturality_on_lower_identities r (n + 1) d.app f hid
    · have hy := lt_of_lt_of_le (r.lt₁ f.hom hf hid) (Nat.le_of_lt_succ x.property)
      rw [app, dite_eq_left hy, app, dite_eq_right hx]
      exact d.outgoing x.obj _ (x := ⟨y.obj, hy⟩) f.hom hf

/-- The actual natural transformation containing all old and newly specified cells. -/
def assemble : lowerInclusion r (n + 1) ⋙ F ⟶ lowerInclusion r (n + 1) ⋙ G :=
  natTransOnLowerOfReedy r (n + 1) d.app d.naturality_inverse d.naturality_direct

lemma assemble_old (j : Lower r n) :
    d.assemble.app ⟨j.obj, lt_trans j.property (Nat.lt_succ_self n)⟩ = old.app j := by
  change d.app _ = _
  exact dite_eq_left j.property

lemma assemble_new (j : J) (hj : r.deg j = n) :
    d.assemble.app ⟨j, hj ▸ Nat.lt_succ_self n⟩ = d.hom j hj := by
  change d.app _ = _
  exact dite_eq_right (hj ▸ Nat.lt_irrefl n)

lemma assemble_restrict : Functor.whiskerLeft (lowerMap r (Nat.le_succ n)) d.assemble = old := by
  apply NatTrans.ext
  funext j
  exact d.assemble_old j

end Data
end SerrePositivity.Reedy.PrescribedLowerStep
