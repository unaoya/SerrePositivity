module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathOperations
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：同じ底を固定する二経路の class 像を、同じ底の相対証人として束ねる。
方針：元の全底経路を後合成し、中点の底の一致で二経路をそろえる。
規約：cell 合成と affine 合成の両方の元の経路を保持する。使われ方：自然性合成の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
open DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  {f g h : W ⟶ C} (v : DGAlgebra.Path.Witness R f g)
  (hv : v.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (N : Bimod B B) (κ : C ⟶ algebra B N) (hκ : κ ≫ projection B N = p)

def relativeClassWitness : RelativeWitness (f ≫ p) N (f ≫ κ) (g ≫ κ) where
  toWitness := v.postcomp κ
  projection_eq := by
    change (v.hom ≫ DGAlgebra.Path.map R κ) ≫ _ = _
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, hκ, hv]

include v hv N κ hκ in
lemma relativeClassWitness_target_base : g ≫ p = f ≫ p := by
  have h := (relativeClassWitness R p v hv N κ hκ).target_projection
  simpa only [Category.assoc, hκ] using h

variable (w : DGAlgebra.Path.Witness R g h)
  (hw : w.hom ≫ DGAlgebra.Path.map R p = (g ≫ p) ≫ DGAlgebra.Path.diagonal R B)

def relativeClassSecond : RelativeWitness (f ≫ p) N (g ≫ κ) (h ≫ κ) :=
  (relativeClassWitness R p w hw N κ hκ).rebase
    (relativeClassWitness_target_base R p v hv N κ hκ)

def relativeClassComposite : RelativeWitness (f ≫ p) N (f ≫ κ) (h ≫ κ) :=
  (relativeClassWitness R p v hv N κ hκ).comp (relativeClassSecond R p v hv N κ hκ w hw)

variable (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n))

def relativeClassCellComposite : RelativeWitness ((cellAugmentation R W ≫ f) ≫ p) N
    ((cellAugmentation R W ≫ f) ≫ κ) ((cellAugmentation R W ≫ h) ≫ κ) :=
  relativeClassWitness R p (RelativePath.cellComp R p hs v w hv hw)
    (RelativePath.cellComp_relative R p hs v w hv hw) N κ hκ

def relativeClassAffineRefined : RelativeWitness ((cellAugmentation R W ≫ f) ≫ p) N
    ((cellAugmentation R W ≫ f) ≫ κ) ((cellAugmentation R W ≫ h) ≫ κ) where
  hom := cellAugmentation R W ≫ (relativeClassComposite R p v hv N κ hκ w hw).hom
  source_eq := by
    rw [Category.assoc, (relativeClassComposite R p v hv N κ hκ w hw).source_eq]
    exact (Category.assoc _ _ _).symm
  target_eq := by
    rw [Category.assoc, (relativeClassComposite R p v hv N κ hκ w hw).target_eq]
    exact (Category.assoc _ _ _).symm
  projection_eq := by
    rw [Category.assoc, (relativeClassComposite R p v hv N κ hκ w hw).projection_eq]
    simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
