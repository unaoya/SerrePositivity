module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：相対 class 経路を、基底射を持つ実平方零代数射で写す。
方針：全経路の底射影を自然性で移し、合成・反転の実 affine 式を比較する。
規約：同じ底上の係数射には限定しない。使われ方：B 遷移後の三経路貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {B C W : Mon (Complex R)}
  {M : Bimod B B} {N : Bimod C C} {q : W ⟶ B}
  (f : B ⟶ C) (k : algebra B M ⟶ algebra C N)
  (hk : k ≫ projection C N = projection B M ≫ f)
  {a b c : W ⟶ algebra B M}

/-- 基底を含む実射による相対経路の移送。 -/
def mapOver (v : RelativeWitness q M a b) : RelativeWitness (q ≫ f) N (a ≫ k) (b ≫ k) where
  toWitness := v.toWitness.postcomp k
  projection_eq := by
    change (v.hom ≫ DGAlgebra.Path.map R k) ≫ _ = _
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, hk, DGAlgebra.Path.map_comp,
      ← Category.assoc, v.projection_eq, Category.assoc, DGAlgebra.Path.diagonal_naturality,
      ← Category.assoc]

lemma mapOver_comp_hom (v : RelativeWitness q M a b) (w : RelativeWitness q M b c) :
    ((v.comp w).mapOver f k hk).hom =
      ((v.mapOver f k hk).comp (w.mapOver f k hk)).hom := by
  apply Mon.Hom.ext
  change ((v.comp w).hom ≫ DGAlgebra.Path.map R k).hom = _
  rw [Mon.comp_hom', comp_hom_linear, comp_hom_linear]
  simp only [add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    DGAlgebra.Path.diagonal_naturality]
  rfl

lemma mapOver_reverse_hom (v : RelativeWitness q M a b) :
    (v.reverse.mapOver f k hk).hom = (v.mapOver f k hk).reverse.hom := by
  apply Mon.Hom.ext
  change (v.reverse.hom ≫ DGAlgebra.Path.map R k).hom = _
  rw [Mon.comp_hom', reverse_hom_linear, reverse_hom_linear]
  simp only [add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    DGAlgebra.Path.diagonal_naturality]
  rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
