module
public import SerrePositivity.DifferentialGraded.Quotient.Erasure
public import Mathlib.Data.ZMod.Basic

/-! # 全path直和の消去作用素と有限pathへの制限の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y : D) : δ 1 2 (erasure A D S x y) = 0 :=
  erasure_closed A D S x y
example (S : Set D) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp (erasure A D S x y) (zero_add 1) =
      eraseRow A D w x y := erasure_precomp A D S x y w
example (b : (Set.univ : Set PUnit.{1})) :
    (Cochain.ofHom (ι (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit [b])).comp
      ((erasure (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit).comp
        (erasure (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit) (by omega))
      (zero_add 2) = 0 := erasure_square_singleton (ZMod 2) PUnit.{1} b _ _

#print axioms DGQuotient.eraseRowCycle
#print axioms DGQuotient.erasureToShift
#print axioms DGQuotient.ι_erasureToShift
#print axioms DGQuotient.erasureCycle
#print axioms DGQuotient.erasure
#print axioms DGQuotient.erasure_closed
#print axioms DGQuotient.erasure_precomp
#print axioms DGQuotient.erasure_originalHom
#print axioms DGQuotient.erasure_square_precomp
#print axioms DGQuotient.erasure_square_originalHom
#print axioms DGQuotient.erasure_square_singleton
