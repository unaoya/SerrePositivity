module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeComposedClass

/-!
概要：普遍的な class 合成を、定数二経路と元の二経路で評価する。
方針：二経路 pullback の両射影と実 affine 式を使う。
規約：全経路の厳密式。使われ方：cell 合成の class 比較正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeComposedPath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

lemma diagonal_first : diagonal R p ≫ first R p = RelativePath.diagonal R p :=
  MonoidPullback.lift_fst _ _ _ _ _

lemma diagonal_second : diagonal R p ≫ second R p = RelativePath.diagonal R p :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma diagonal_middle : diagonal R p ≫ middle R p = 𝟙 C := by
  rw [middle, ← Category.assoc, diagonal_first, RelativePath.diagonal_target]

variable (N : Bimod B B) (κ : C ⟶ SquareZero.algebra B N) (hκ : κ ≫ SquareZero.projection B N = p)

lemma classFirst_diagonal : diagonal R p ≫ (classFirst R p N κ hκ).hom =
    κ ≫ Path.diagonal R (SquareZero.algebra B N) := by
  change diagonal R p ≫ ((first R p ≫ RelativePath.inclusion R p) ≫ Path.map R κ) = _
  simp only [Category.assoc, reassoc_of% (diagonal_first R p),
    reassoc_of% (RelativePath.diagonal_inclusion R p), Path.diagonal_naturality]

lemma classSecond_diagonal : diagonal R p ≫ (classSecond R p N κ hκ).hom =
    κ ≫ Path.diagonal R (SquareZero.algebra B N) := by
  change diagonal R p ≫ ((second R p ≫ RelativePath.inclusion R p) ≫ Path.map R κ) = _
  simp only [Category.assoc, reassoc_of% (diagonal_second R p),
    reassoc_of% (RelativePath.diagonal_inclusion R p), Path.diagonal_naturality]

lemma classComposition_diagonal : diagonal R p ≫ (classComposition R p N κ hκ).hom =
    κ ≫ Path.diagonal R (SquareZero.algebra B N) := by
  apply Mon.Hom.ext
  have h := congrArg (fun k => (diagonal R p).hom ≫ k)
    (SquareZero.RelativeWitness.comp_hom_linear (classFirst R p N κ hκ)
      (classSecond R p N κ hκ))
  simpa only [comp_add, comp_sub, ← Mon.comp_hom', Category.assoc,
    classFirst_diagonal, classSecond_diagonal, reassoc_of% (diagonal_middle R p),
    Category.id_comp, sub_self, zero_add] using! h

variable {W : Mon (Complex R)} {f g h : W ⟶ C} (v : Path.Witness R f g) (w : Path.Witness R g h)
  (hv : v.hom ≫ Path.map R p = (f ≫ p) ≫ Path.diagonal R B)
  (hw : w.hom ≫ Path.map R p = (g ≫ p) ≫ Path.diagonal R B)

lemma lift_first : lift R p v w hv hw ≫ first R p = RelativePath.witnessLift R p v hv :=
  MonoidPullback.lift_fst _ _ _ _ _

lemma lift_second : lift R p v w hv hw ≫ second R p = RelativePath.witnessLift R p w hw :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma lift_middle : lift R p v w hv hw ≫ middle R p = g := by
  rw [middle, ← Category.assoc, lift_first, RelativePath.witnessLift_target]

lemma classFirst_lift : lift R p v w hv hw ≫ (classFirst R p N κ hκ).hom =
    v.hom ≫ Path.map R κ := by
  change lift R p v w hv hw ≫ ((first R p ≫ RelativePath.inclusion R p) ≫ Path.map R κ) = _
  simp only [Category.assoc, reassoc_of% (lift_first R p v w hv hw),
    reassoc_of% (RelativePath.witnessLift_inclusion R p v hv)]

lemma classSecond_lift : lift R p v w hv hw ≫ (classSecond R p N κ hκ).hom =
    w.hom ≫ Path.map R κ := by
  change lift R p v w hv hw ≫ ((second R p ≫ RelativePath.inclusion R p) ≫ Path.map R κ) = _
  simp only [Category.assoc, reassoc_of% (lift_second R p v w hv hw),
    reassoc_of% (RelativePath.witnessLift_inclusion R p w hw)]

lemma classComposition_lift_hom : (lift R p v w hv hw ≫ (classComposition R p N κ hκ).hom).hom =
    (v.hom ≫ Path.map R κ).hom -
      (g ≫ κ ≫ Path.diagonal R (SquareZero.algebra B N)).hom + (w.hom ≫ Path.map R κ).hom := by
  have he := congrArg (fun k => (lift R p v w hv hw).hom ≫ k)
    (SquareZero.RelativeWitness.comp_hom_linear (classFirst R p N κ hκ)
      (classSecond R p N κ hκ))
  simpa only [comp_add, comp_sub, ← Mon.comp_hom', Category.assoc,
    classFirst_lift, classSecond_lift, reassoc_of% (lift_middle R p v w hv hw)] using! he

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeComposedPath
