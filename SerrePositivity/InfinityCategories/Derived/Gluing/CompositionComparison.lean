module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrimitiveComparison

/-! 元の全 gluing Hom tensor 上で、合成の第三 cochain を厳密に回収する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)

/-- 全 Hom tensor を代表加群表示へ移し、同じ二項の比較 cochain を回収する。 -/
def dgGluingCompositePrimitive :
    Cochain (dgGluingHomComplex R C D M X Y ⊗ dgGluingHomComplex R C D M Y Z)
      (M.value X.left Z.right) (-1) :=
  ((Cochain.ofHom ((dgGluingHomRepresentableIso R C D M X Y).hom ⊗ₘ
      (dgGluingHomRepresentableIso R C D M Y Z).hom)).comp
    (dgFunctorCommaCompositePrimitive R D (RightModule R C) M.toFunctor
      (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)
      (dgGluingCommaObject R C D M Z)) (zero_add (-1))).comp
    (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Z.right)).hom) (add_zero (-1))

/-- 移した二項の cochain は、native 合成の実第三成分そのものである。 -/
lemma dgGluingComposition_comparison :
    dgGluingHomComparison R C D M X Z _ (dgGluingComposition R C D M X Y Z) =
      dgGluingCompositePrimitive R C D M X Y Z := by
  have h := dgGluingHomComparison_yoneda R C D M X Z _
    (dgGluingComposition R C D M X Y Z)
  have hc := (dgGluingToComma R C D M).map_comp X Y Z
  change dgGluingComposition R C D M X Y Z ≫
    (dgGluingHomRepresentableIso R C D M X Z).hom =
      ((dgGluingHomRepresentableIso R C D M X Y).hom ⊗ₘ
        (dgGluingHomRepresentableIso R C D M Y Z).hom) ≫
          dgFunctorCommaComposition R D (RightModule R C) M.toFunctor
            (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)
            (dgGluingCommaObject R C D M Z) at hc
  rw [hc, dgFunctorCommaHomComparison_precompose,
    dgFunctorCommaComposition_comparison] at h
  exact h.symm

end SerrePositivity.InfinityCategories
