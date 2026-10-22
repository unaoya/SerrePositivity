module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomCoefficientComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaBottomActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.YonedaCoefficientPostInverse
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComparisonProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.Projections

/-! 実係数包含の後合成を、元の双加群の共変作用と全次数で同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingCrossHomCoefficientMap_post
    (X : DGGluingCFactor R C D M) (Y Z : DGGluingDFactor R C D M)
    {q p n : ℤ} (t : ((M.value X.val.left Y.val.right)⟦(-1 : ℤ)⟧).X q)
    (g : (homObject R (DGGluingObject R C D M) Y.val Z.val).X p) (hn : q + p = n) :
    forward R (x := X.val) (y := Y.val) (z := Z.val)
      ((dgGluingCrossHomCoefficientMap R C D M X Y).f q t) g hn =
    (dgGluingCrossHomCoefficientMap R C D M X Z).f n
      (((q - 1) * p).negOnePow •
        ((moduleHomπ R C (M.rightAt Y.val.right) (M.rightAt Z.val.right) X.val.left).f p
          ((M.toFunctor.map Y.val.right Z.val.right).f p
            ((dgGluingRightHomMap R C D M Y.val Z.val).f p g))).v
          (q - 1) (n - 1) (by omega) t) := by
  apply (ModuleCat.mono_iff_injective
    ((dgGluingHomRepresentableIso R C D M X.val Z.val).hom.f n)).mp inferInstance
  have hm := DGFunctor.map_forward R (dgGluingToComma R C D M)
    (x := X.val) (y := Y.val) (z := Z.val)
    ((dgGluingCrossHomCoefficientMap R C D M X Y).f q t) g hn
  change (dgGluingHomRepresentableIso R C D M X.val Z.val).hom.f n
      (forward R (x := X.val) (y := Y.val) (z := Z.val)
        ((dgGluingCrossHomCoefficientMap R C D M X Y).f q t) g hn) = _ at hm
  refine hm.trans ?_
  change forward R
    (x := dgGluingCommaObject R C D M X.val)
    (y := dgGluingCommaObject R C D M Y.val)
    (z := dgGluingCommaObject R C D M Z.val)
    ((dgGluingHomRepresentableIso R C D M X.val Y.val).hom.f q
      ((dgGluingCrossHomCoefficientMap R C D M X Y).f q t))
    ((dgGluingHomRepresentableIso R C D M Y.val Z.val).hom.f p g) hn = _
  rw [dgGluingCrossHomCoefficientMap_comma_apply R C D M X Y q t,
    dgGluingCrossHomCoefficientMap_comma_apply R C D M X Z n]
  rw [dgGluingCommaBottom_forward R D (RightModule R C) M.toFunctor
    (dgGluingCommaObject R C D M X.val) (dgGluingCommaObject R C D M Y.val)
    (dgGluingCommaObject R C D M Z.val) hn]
  have hr := congrArg (fun k => k.f p g)
    (dgGluingHomRepresentableIso_right R C D M Y.val Z.val)
  change (dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor
      (dgGluingCommaObject R C D M Y.val) (dgGluingCommaObject R C D M Z.val)).f p
      ((dgGluingHomRepresentableIso R C D M Y.val Z.val).hom.f p g) =
    (dgGluingRightHomMap R C D M Y.val Z.val).f p g at hr
  change (dgGluingCommaBottomInclusion R D (RightModule R C) M.toFunctor
      (dgGluingCommaObject R C D M X.val) (dgGluingCommaObject R C D M Z.val)).f n
      (forward R (x := representable R X.val.left) (y := M.rightAt Y.val.right)
        (z := M.rightAt Z.val.right) (p := q - 1) (q := p) (n := n - 1)
        ((dgYonedaIso R X.val.left (M.rightAt Y.val.right)).inv.f (q - 1) t)
        ((M.toFunctor.map Y.val.right Z.val.right).f p
          ((dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor
            (dgGluingCommaObject R C D M Y.val) (dgGluingCommaObject R C D M Z.val)).f p
            ((dgGluingHomRepresentableIso R C D M Y.val Z.val).hom.f p g)))
        (by omega)) = _
  rw [hr, dgGluingYonedaCoefficient_post_inv R C X.val.left
    (M.rightAt Y.val.right) (M.rightAt Z.val.right)
    (q := q - 1) (p := p) (n := n - 1)]

end SerrePositivity.InfinityCategories
