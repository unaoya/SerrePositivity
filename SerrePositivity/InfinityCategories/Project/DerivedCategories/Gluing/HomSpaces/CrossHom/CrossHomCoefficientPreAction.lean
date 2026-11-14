module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.CrossHomCoefficientComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.CommaBottomActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.YonedaCoefficientActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomComparisonProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Projections

/-! 実係数包含の前合成は、元の双加群の反変作用と全次数で一致する。 -/
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

lemma dgGluingCrossHomCoefficientMap_pre
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M)
    {q p n : ℤ} (b : (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X.val Y.val).X q)
    (t : ((M.value Y.val.left Z.val.right)⟦(-1 : ℤ)⟧).X p) (hn : q + p = n) :
    forward R (x := X.val) (y := Y.val) (z := Z.val)
      b ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M Y Z).f p t) hn =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Z).f n
      (q.negOnePow • moduleAction R (M.rightAt Z.val.right)
        (x := op Y.val.left) (y := op X.val.left)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X.val Y.val).f q b) t (by omega : (p - 1) + q = n - 1)) := by
  apply (ModuleCat.mono_iff_injective
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Z.val).hom.f n)).mp inferInstance
  have hm := DGFunctor.map_forward R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (x := X.val) (y := Y.val) (z := Z.val) b
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M Y Z).f p t) hn
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Z.val).hom.f n
      (forward R (x := X.val) (y := Y.val) (z := Z.val) b
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M Y Z).f p t) hn) = _ at hm
  refine hm.trans ?_
  change forward R
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val)
    (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val)
    (z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Y.val).hom.f q b)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y.val Z.val).hom.f p
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M Y Z).f p t)) hn = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap_comma_apply R C D M Y Z p t,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap_comma_apply R C D M X Z n]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComma_forward_bottom R D (RightModule R C) M.toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val) hn]
  have hl := congrArg (fun k => k.f q b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_left R C D M X.val Y.val)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val)).f q
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Y.val).hom.f q b) =
    (yonedaHom R C X.val.left Y.val.left).f q
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X.val Y.val).f q b) at hl
  rw [hl]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBottomInclusion R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z.val)).f n
      (q.negOnePow • forward R
        (x := representable R X.val.left) (y := representable R Y.val.left)
        (z := M.rightAt Z.val.right) (p := q) (q := p - 1) (n := n - 1)
        ((yonedaHom R C X.val.left Y.val.left).f q
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X.val Y.val).f q b))
        ((dgYonedaIso R Y.val.left (M.rightAt Z.val.right)).inv.f (p - 1) t)
        (by omega)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaCoefficient_pre_inv R C X.val.left Y.val.left
    (M.rightAt Z.val.right) (q := q) (p := p - 1) (n := n - 1)]
  simp only [Units.smul_def, map_zsmul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
