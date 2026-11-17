module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraMappingSpace

/-!
# Cofibrant E 代数の Map^h の比較を元の射で正規化する

概要：Hovey §5・Dwyer–Kan の零次の比較で元の cofibrant 代数射を回収する。
方針：同じ包含の因子化同型の自然性と元の Map^h の類の式を使う。
規約：元の代数射から作った同じ零単体の類を使う。
使われ方：単体的局所化の比較の零次の正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra Opposite

variable (A : Type u) [CommRing A]

/-- 概要：同じ Map^h の元の射の類は cofibrant 相対圏での局所化像（Hovey §5）。
方針：元の全代数側の類の計算と包含の因子化同型の自然性を合成する。
規約：元の射・零単体・普通の局所化を保持する。
使われ方：DK 比較で元の射の零次の像を照合する。 -/
lemma cofibrantAlgebraMappingSpacePiZeroEquiv_class {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraMappingSpacePiZeroEquiv A X Y
        (mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f)) =
      (cofibrantAlgebraWeakEquivalences A).Q.map f := by
  let := modelCategory A
  let Q := (weakEquivalences (operad A).Algebra).Q
  let R := (cofibrantAlgebraWeakEquivalences A).Q
  let E := cofibrantAlgebraHoEquivalence A
  let i := cofibrantAlgebraInclusionLocalizedIso A
  apply E.fullyFaithfulFunctor.homEquiv.injective
  change E.fullyFaithfulFunctor.homEquiv
      (E.fullyFaithfulFunctor.homEquiv.symm
        ((i.app X).inv ≫ mappingSpacePiZeroEquiv A Q
          (op ((cofibrantAlgebraInclusion A).obj X))
          ((cofibrantAlgebraInclusion A).obj Y)
          (mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f)) ≫ (i.app Y).hom)) = _
  rw [Equiv.apply_symm_apply, mappingSpacePiZeroEquiv_class]
  have h := i.hom.naturality f
  change Q.map ((cofibrantAlgebraInclusion A).map f) ≫ (i.app Y).hom =
    (i.app X).hom ≫ E.functor.map (R.map f) at h
  calc
    _ = (i.app X).inv ≫ ((i.app X).hom ≫ E.functor.map (R.map f)) :=
      congrArg (fun z => (i.app X).inv ≫ z) h
    _ = E.functor.map (R.map f) := (i.app X).inv_hom_id_assoc _

end SerrePositivity.EInfinity.BarrattEccles
