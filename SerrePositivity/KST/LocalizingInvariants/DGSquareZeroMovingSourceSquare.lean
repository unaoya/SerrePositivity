module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSourceSlideFaces
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeDoublePath

/-!
概要：零底で一定の source 正方形を、指定した動く底を保つ実二重経路へ持ち上げる。
方針：右脚の内対角と零底の sourceSlide を、平方零底変更の実 pullback で貼り合わせる。
規約：元の底経路と全零底 class 経路を保持。使われ方：底が動く W の模型比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B T : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  (r : T ⟶ DGAlgebra.Path.algebra R A) (q₀ : T ⟶ B)
  (hr : r ≫ DGAlgebra.Path.map R q = q₀ ≫ DGAlgebra.Path.diagonal R B)
  {x y z : T ⟶ algebra B N} (v : RelativeWitness q₀ N x y) (p : RelativeWitness q₀ N x z)

include hr in
lemma movingSourceBase_condition :
    (r ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R A)) ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.map R q) =
    (q₀ ≫ DGAlgebra.Path.diagonal R B) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B) := by
  rw [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_naturality,
    DGAlgebra.Path.map_comp, ← Category.assoc, hr, Category.assoc,
    DGAlgebra.Path.diagonal_naturality]
  simp only [Category.assoc]

def movingSourceSquare : T ⟶ DGAlgebra.Path.algebra R
    (DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))) :=
  baseChangeDoublePathLift q N (r ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R A))
    (v.sourceSlideHom p) ((movingSourceBase_condition q r q₀ hr).trans
      (RelativeWitness.sourceSlideHom_projection v p).symm)

lemma movingSourceSquare_projection : movingSourceSquare q N r q₀ hr v p ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection A (bimoduleRestrict q N))) =
      r ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R A) :=
  baseChangeDoublePathLift_projection _ _ _ _ _

lemma movingSourceSquare_map : movingSourceSquare q N r q₀ hr v p ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (baseChangeMap q N)) = v.sourceSlideHom p :=
  baseChangeDoublePathLift_map _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZero
