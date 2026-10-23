module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceSquare

/-!
概要：動く底へ持ち上げた source 正方形の内側二辺を、元の native 経路へ同定する。
方針：底の内対角と零底 sourceSlide の四辺を二射影で比較する。
規約：全 source class 経路と動く右脚を保持。使われ方：W の実模型 path lift。
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

lemma movingSourceSquare_innerSource_eq
    (hu : u ≫ DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) = r)
    (hk : u ≫ DGAlgebra.Path.map R (baseChangeMap q N) = v.hom) :
    movingSourceSquare q N r q₀ hr v p ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra A (bimoduleRestrict q N))) = u := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_source,
      DGAlgebra.Path.map_comp, ← Category.assoc, movingSourceSquare_projection,
      Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_source,
      DGAlgebra.Path.map_id, Category.comp_id]
    exact hu.symm
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_source,
      DGAlgebra.Path.map_comp, ← Category.assoc, movingSourceSquare_map,
      RelativeWitness.sourceSlideHom_source_trace]
    exact hk.symm

lemma movingSourceSquare_innerTarget_eq
    (hu : u ≫ DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) = r)
    (hk : u ≫ DGAlgebra.Path.map R (baseChangeMap q N) =
      z ≫ DGAlgebra.Path.diagonal R (algebra B N)) :
    movingSourceSquare q N r q₀ hr v p ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra A (bimoduleRestrict q N))) = u := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_target,
      DGAlgebra.Path.map_comp, ← Category.assoc, movingSourceSquare_projection,
      Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_target,
      DGAlgebra.Path.map_id, Category.comp_id]
    exact hu.symm
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_target,
      DGAlgebra.Path.map_comp, ← Category.assoc, movingSourceSquare_map,
      RelativeWitness.sourceSlideHom_target_trace]
    exact hk.symm

lemma movingSourceSquare_innerTarget_zero (hz : z = q₀ ≫ zeroSection B N) :
    movingSourceSquare q N r q₀ hr v p ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra A (bimoduleRestrict q N))) =
    r ≫ DGAlgebra.Path.map R (zeroSection A (bimoduleRestrict q N)) := by
  apply movingSourceSquare_innerTarget_eq
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, zeroSection_projection,
      DGAlgebra.Path.map_id, Category.comp_id]
  · have hk : zeroSection A (bimoduleRestrict q N) ≫ baseChangeMap q N =
        q ≫ zeroSection B N := zeroSection_mapOver q (bimoduleRestrict q N) N (𝟙 _)
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, hk, DGAlgebra.Path.map_comp,
      ← Category.assoc, hr, Category.assoc, DGAlgebra.Path.diagonal_naturality, hz,
      Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
