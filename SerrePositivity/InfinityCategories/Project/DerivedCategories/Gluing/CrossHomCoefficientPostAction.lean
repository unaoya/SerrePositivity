module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CrossHomCoefficientComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaBottomActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.YonedaCoefficientPostInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomComparisonProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Projections

/-! 実係数包含の後合成を、元の双加群の共変作用と全次数で同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingCrossHomCoefficientMap_post
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M)
    {q p n : ℤ} (t : ((M.value X.val.left Y.val.right)⟦(-1 : ℤ)⟧).X q)
    (g : (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) Y.val Z.val).X p) (hn : q + p = n) :
    forward R (x := X.val) (y := Y.val) (z := Z.val)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Y).f q t) g hn =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Z).f n
      (((q - 1) * p).negOnePow •
        ((moduleHomπ R C (M.rightAt Y.val.right) (M.rightAt Z.val.right) X.val.left).f p
          ((M.toFunctor.map Y.val.right Z.val.right).f p
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y.val Z.val).f p g))).v
          (q - 1) (n - 1) (by omega) t) := by
  apply (ModuleCat.mono_iff_injective
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Z.val).hom.f n)).mp inferInstance
  have hm := DGFunctor.map_forward R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (x := X.val) (y := Y.val) (z := Z.val)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Y).f q t) g hn
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Z.val).hom.f n
      (forward R (x := X.val) (y := Y.val) (z := Z.val)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Y).f q t) g hn) = _ at hm
  refine hm.trans ?_
  change forward R
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val)
    (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val)
    (z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Y.val).hom.f q
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Y).f q t))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y.val Z.val).hom.f p g) hn = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap_comma_apply R C D M X Y q t,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap_comma_apply R C D M X Z n]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBottom_forward R D (RightModule R C) M.toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val) hn]
  have hr := congrArg (fun k => k.f p g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_right R C D M Y.val Z.val)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val)).f p
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y.val Z.val).hom.f p g) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y.val Z.val).f p g at hr
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBottomInclusion R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val)).f n
      (forward R (x := representable R X.val.left) (y := M.rightAt Y.val.right)
        (z := M.rightAt Z.val.right) (p := q - 1) (q := p) (n := n - 1)
        ((dgYonedaIso R X.val.left (M.rightAt Y.val.right)).inv.f (q - 1) t)
        ((M.toFunctor.map Y.val.right Z.val.right).f p
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val)).f p
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y.val Z.val).hom.f p g)))
        (by omega)) = _
  rw [hr, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaCoefficient_post_inv R C X.val.left
    (M.rightAt Y.val.right) (M.rightAt Z.val.right)
    (q := q - 1) (p := p) (n := n - 1)]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
