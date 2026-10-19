module

public import SerrePositivity.KST.Spectra.BoundaryTensorMonomorphism

/-!
概要：任意の二つの単体集合の単射の pushout-product は単射。
方針：各射をその range の部分複体包含へ同型にし、部分複体の積の和の包含へ送る。
規約：境界包含だけに限らず、任意の実際の pushout-product 正方形に適用する。
使われ方：Goerss–Jardine VII §4。Reedy cofibrant な重みの境界 cylinder の単射性。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PushoutProductMonomorphism
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 単射をその range の部分複体包含と厳密に比較する arrow 同型。 -/
def rangeArrowIso {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Arrow.mk i ≅ Arrow.mk (Subcomplex.range i).ι :=
  Arrow.isoMk (asIso (Subcomplex.toRange i)) (Iso.refl _) (by
    change Subcomplex.toRange i ≫ (Subcomplex.range i).ι = i ≫ 𝟙 B
    rw [Subcomplex.toRange_ι, Category.comp_id])

/-- 任意の二つの単射の任意の pushout-product は単射。 -/
lemma mono {A B C D : SSet.{u}} {i : A ⟶ B} {j : C ⟶ D} [Mono i] [Mono j]
    (s : (curriedTensor SSet.{u}).PushoutObjObj i j) : Mono s.ι := by
  let t := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let e₁ := (MonoidalCategory.Arrow.pushoutProduct.mapIso (rangeArrowIso i)).app (Arrow.mk j)
  let e₂ := (MonoidalCategory.Arrow.pushoutProduct.obj
    (Arrow.mk (Subcomplex.range i).ι)).mapIso (rangeArrowIso j)
  let e : Arrow.mk s.ι ≅ Arrow.mk ((Subcomplex.range i).unionProd (Subcomplex.range j)).ι :=
    SimplexTensorBoundary.productSquareArrowIso s t ≪≫ e₁ ≪≫ e₂ ≪≫
      (Subcomplex.unionProd.ιIso (Subcomplex.range i) (Subcomplex.range j)).symm
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff e).mpr
    (inferInstanceAs (Mono ((Subcomplex.range i).unionProd (Subcomplex.range j)).ι))

end
end SerrePositivity.KST.Spectra.PushoutProductMonomorphism
