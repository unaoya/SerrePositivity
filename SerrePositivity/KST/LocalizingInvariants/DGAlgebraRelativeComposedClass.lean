module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeComposedPath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness

/-!
概要：相対二経路の実代数上で、class 射後の二経路を同じ底上で実 affine 合成する。
方針：元の二経路の射影と中点の等式から二つの相対 class 証人を作る。
規約：全合成は実代数射。使われ方：cell 経路合成と affine class 合成の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeComposedPath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)
  (N : Bimod B B) (κ : C ⟶ SquareZero.algebra B N) (hκ : κ ≫ SquareZero.projection B N = p)

def middle : algebra R p ⟶ C := first R p ≫ RelativePath.target R p

lemma middle_base : middle R p ≫ p = source R p ≫ p := by
  simp only [middle, source, Category.assoc, RelativePath.target_projection,
    RelativePath.source_projection]

lemma second_projection : second R p ≫ RelativePath.projection R p = source R p ≫ p := by
  rw [← RelativePath.source_projection, ← Category.assoc, ← condition,
    Category.assoc, RelativePath.target_projection]
  simp only [source, Category.assoc, RelativePath.source_projection]

def classFirst : SquareZero.RelativeWitness (source R p ≫ p) N
    (source R p ≫ κ) (middle R p ≫ κ) where
  hom := (first R p ≫ RelativePath.inclusion R p) ≫ Path.map R κ
  source_eq := by
    simp only [Category.assoc, Path.map_source, source, RelativePath.source]
  target_eq := by
    simp only [Category.assoc, Path.map_target, middle, RelativePath.target]
  projection_eq := by
    rw [Category.assoc, ← Path.map_comp, hκ, Category.assoc, RelativePath.condition]
    simp only [source, Category.assoc, RelativePath.source_projection]

def classSecond : SquareZero.RelativeWitness (source R p ≫ p) N
    (middle R p ≫ κ) (target R p ≫ κ) where
  hom := (second R p ≫ RelativePath.inclusion R p) ≫ Path.map R κ
  source_eq := by
    calc
      _ = (second R p ≫ RelativePath.source R p) ≫ κ := by
        simp only [Category.assoc, Path.map_source, RelativePath.source]
      _ = (first R p ≫ RelativePath.target R p) ≫ κ :=
        congrArg (fun k => k ≫ κ) (condition R p).symm
      _ = _ := rfl
  target_eq := by
    simp only [Category.assoc, Path.map_target, target, RelativePath.target]
  projection_eq := by
    rw [Category.assoc, ← Path.map_comp, hκ, Category.assoc, RelativePath.condition,
      ← Category.assoc, second_projection]

def classComposition : SquareZero.RelativeWitness (source R p ≫ p) N
    (source R p ≫ κ) (target R p ≫ κ) :=
  (classFirst R p N κ hκ).comp (classSecond R p N κ hκ)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeComposedPath
