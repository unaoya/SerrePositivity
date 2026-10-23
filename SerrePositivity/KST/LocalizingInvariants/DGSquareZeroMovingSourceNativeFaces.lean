module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceOuterFaces
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceInnerFaces
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraDoublePathIsoFaces
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor

/-!
概要：動く底の正方形を元の係数へ戻し、指定した native 四辺を回収する。
方針：係数同型とその逆で二重経路を移送し、二射影の一意性を使う。
規約：底と全 class 経路を保持。使われ方：元の Postnikov W の模型経路。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
open DGAlgebra
variable {R : Type u} [CommRing R] {A B T : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  {M : Bimod A A} (e : M ≅ bimoduleRestrict q N)
  (r : T ⟶ DGAlgebra.Path.algebra R A) (q₀ : T ⟶ B)
  (hr : r ≫ DGAlgebra.Path.map R q = q₀ ≫ DGAlgebra.Path.diagonal R B)
  {x y z : T ⟶ algebra B N} (v : RelativeWitness q₀ N x y) (p : RelativeWitness q₀ N x z)
  (u : T ⟶ DGAlgebra.Path.algebra R (algebra A M))

def movingSourceNativeSquare := DGAlgebra.Path.pullbackDoubleIso R (coefficientIso A e)
  (movingSourceSquare q N r q₀ hr v p)

lemma nativePath_projection (a : T ⟶ DGAlgebra.Path.algebra R A)
    (h : u ≫ DGAlgebra.Path.map R (projection A M) = a) :
    (u ≫ DGAlgebra.Path.map R (coefficientIso A e).hom) ≫
      DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) = a := by
  rw [Category.assoc, ← DGAlgebra.Path.map_comp, coefficientIso_hom,
    coefficientMap_projection]
  exact h

lemma movingSourceNativeSquare_source
    (hu : u ≫ DGAlgebra.Path.map R (projection A M) =
      (r ≫ DGAlgebra.Path.source R A) ≫ DGAlgebra.Path.diagonal R A)
    (hk : u ≫ DGAlgebra.Path.map R ((coefficientIso A e).hom ≫ baseChangeMap q N) = p.hom) :
    movingSourceNativeSquare q N e r q₀ hr v p ≫
      DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra A M)) = u := by
  apply DGAlgebra.Path.pullbackDoubleIso_source
  apply movingSourceSquare_source_eq
  · exact nativePath_projection q N e u _ hu
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp]; exact hk

lemma movingSourceNativeSquare_target
    (hu : u ≫ DGAlgebra.Path.map R (projection A M) =
      (r ≫ DGAlgebra.Path.target R A) ≫ DGAlgebra.Path.diagonal R A)
    (hk : u ≫ DGAlgebra.Path.map R ((coefficientIso A e).hom ≫ baseChangeMap q N) =
      (v.reverse.comp p).hom) :
    movingSourceNativeSquare q N e r q₀ hr v p ≫
      DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra A M)) = u := by
  apply DGAlgebra.Path.pullbackDoubleIso_target
  apply movingSourceSquare_target_eq
  · exact nativePath_projection q N e u _ hu
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp]; exact hk

lemma movingSourceNativeSquare_innerSource
    (hu : u ≫ DGAlgebra.Path.map R (projection A M) = r)
    (hk : u ≫ DGAlgebra.Path.map R ((coefficientIso A e).hom ≫ baseChangeMap q N) = v.hom) :
    movingSourceNativeSquare q N e r q₀ hr v p ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra A M)) = u := by
  apply DGAlgebra.Path.pullbackDoubleIso_innerSource
  apply movingSourceSquare_innerSource_eq
  · exact nativePath_projection q N e u _ hu
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp]; exact hk

lemma movingSourceNativeSquare_innerTarget
    (hu : u ≫ DGAlgebra.Path.map R (projection A M) = r)
    (hk : u ≫ DGAlgebra.Path.map R ((coefficientIso A e).hom ≫ baseChangeMap q N) =
      z ≫ DGAlgebra.Path.diagonal R (algebra B N)) :
    movingSourceNativeSquare q N e r q₀ hr v p ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra A M)) = u := by
  apply DGAlgebra.Path.pullbackDoubleIso_innerTarget
  apply movingSourceSquare_innerTarget_eq
  · exact nativePath_projection q N e u _ hu
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp]; exact hk

end SerrePositivity.KST.LocalizingInvariants.SquareZero
