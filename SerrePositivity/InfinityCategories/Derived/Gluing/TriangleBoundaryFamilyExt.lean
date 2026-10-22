module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TriangleBoundaryFamily

/-! パラメーター付き境界図式は、合成ホーンと対角辺への制限で決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
variable {T X : SSet.{u}}

lemma dgGluingTriangleBoundaryFamily_hom_ext
    {f g : (boundary 2 : SSet.{u}) ⊗ T ⟶ X}
    (hh : (Subcomplex.homOfLE triangleBoundary_bicartSq.le₂₄ ▷ T) ≫ f =
      (Subcomplex.homOfLE triangleBoundary_bicartSq.le₂₄ ▷ T) ≫ g)
    (hd : (boundary.ι (1 : Fin 3) ▷ T) ≫ f = (boundary.ι (1 : Fin 3) ▷ T) ≫ g) :
    f = g := by
  apply (triangleBoundary_isPushout.map (tensorRight T)).hom_ext
  · simpa only [tensorRight, Functor.flip, curriedTensor] using hh
  · apply (cancel_epi (triangleDiagonalFaceIso.hom ▷ T)).mp
    simpa only [tensorRight, Functor.flip, curriedTensor, ← Category.assoc,
      ← comp_whiskerRight, triangleDiagonalFaceIso_hom_boundary] using hd

end SerrePositivity.InfinityCategories
