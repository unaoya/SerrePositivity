module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CrossHomFunctorMaps

/-! 全次数評価における二関手の作用。shift の符号を明示して保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M

lemma dgGluingCrossHomFunctor_map_apply
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M)
    {p q n : ℤ} (g : (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) Y.val Z.val).X p)
    (t : (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X.val Y.val).X q) (hn : q + p = n) :
    ((moduleHomπ R A _ _ X).f p
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M).map Y Z).f p g)).v q n hn t =
    (p * q).negOnePow • forward R (x := X.val) (y := Y.val) (z := Z.val) t g hn := by
  have he := congrArg (fun k => k.f p g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor_map_π R C D M X Y Z)
  change (moduleHomπ R A _ _ X).f p
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M).map Y Z).f p g) =
    (moduleHomπ R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (representable R Y.val)
      (representable R Z.val) X.val).f p
      ((yonedaHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) Y.val Z.val).f p g) at he
  rw [he]
  change ((moduleHomπ R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (representable R Y.val)
    (representable R Z.val) X.val).f p
    ((yonedaHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) Y.val Z.val).f p g)).v q n hn t = _
  exact yonedaHom_element R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) Y.val Z.val X.val g t hn

lemma dgGluingCrossCoefficientFunctor_map_apply
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M)
    {p q n : ℤ} (g : (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) Y.val Z.val).X p)
    (t : ((M.value X.val.left Y.val.right)⟦(-1 : ℤ)⟧).X q) (hn : q + p = n) :
    ((moduleHomπ R A _ _ X).f p
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M).map Y Z).f p g)).v q n hn t =
    ((-1 : ℤ) * p).negOnePow •
      ((moduleHomπ R C (M.rightAt Y.val.right) (M.rightAt Z.val.right) X.val.left).f p
        ((M.toFunctor.map Y.val.right Z.val.right).f p
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y.val Z.val).f p g))).v
        (q - 1) (n - 1) (by omega) t := by
  have he := congrArg (fun k => (k.f p g).v q n hn t)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor_map_π R C D M X Y Z)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, shiftHom_v] using! he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
