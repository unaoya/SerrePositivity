module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceSquare

/-!
概要：動く底へ持ち上げた source 正方形の外側両端を、元の全経路へ同定する。
方針：底と零底 class への二射影の一意性を使う。
規約：両端の全 native 経路を回収。使われ方：W の模型経路の始点・終点。
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
  (u : T ⟶ DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N)))

lemma movingSourceSquare_source_eq
    (hu : u ≫ DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) =
      (r ≫ DGAlgebra.Path.source R A) ≫ DGAlgebra.Path.diagonal R A)
    (hk : u ≫ DGAlgebra.Path.map R (baseChangeMap q N) = p.hom) :
    movingSourceSquare q N r q₀ hr v p ≫ DGAlgebra.Path.source R
      (DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))) = u := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
      movingSourceSquare_projection, Category.assoc, DGAlgebra.Path.map_source,
      ← Category.assoc]
    exact hu.symm
  · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
      movingSourceSquare_map, RelativeWitness.sourceSlideHom_source]
    exact hk.symm

lemma movingSourceSquare_target_eq
    (hu : u ≫ DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) =
      (r ≫ DGAlgebra.Path.target R A) ≫ DGAlgebra.Path.diagonal R A)
    (hk : u ≫ DGAlgebra.Path.map R (baseChangeMap q N) = (v.reverse.comp p).hom) :
    movingSourceSquare q N r q₀ hr v p ≫ DGAlgebra.Path.target R
      (DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))) = u := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
      movingSourceSquare_projection, Category.assoc, DGAlgebra.Path.map_target,
      ← Category.assoc]
    exact hu.symm
  · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
      movingSourceSquare_map, RelativeWitness.sourceSlideHom_target]
    exact hk.symm

end SerrePositivity.KST.LocalizingInvariants.SquareZero
