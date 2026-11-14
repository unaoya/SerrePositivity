module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaCategory
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-! comma 合成の第三 cochain の第一項を、実斉次元の式へ回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) {p q n : ℤ}
  (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y).X q)
  (g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z).X p) (hn : q + p = n)

/-- 第一比較項は、元の比較成分と後続射の像成分の実斉次合成。 -/
lemma dgGluingCommaFirstPrimitive_element :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) =
    forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega) b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega : q - 1 + p = n - 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive, cochain_comp_ofHom_apply,
    tensorRightHom_apply_of_sum _ _ _ (-1) q p n (q - 1) (n - 1) hn (by omega) (by omega)]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    tensorHom_def, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    SerrePositivity.DifferentialGraded.whiskerRight_apply,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply]
  rfl

/-- 後続斉次射の第三成分が零なら、第二比較項の同じ値も零。 -/
lemma dgGluingCommaSecondPrimitive_element_zero
    (hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive, cochain_comp_ofHom_apply,
    tensorLeftHom_apply_of_sum _ _ _ (-1) q p n (p - 1) (n - 1) hn (by omega) (by omega)]
  simp only [hg, TensorProduct.tmul_zero, map_zero, smul_zero]

/-- 第三成分零の後続射との合成は、第一比較項だけで元の第三成分を運ぶ。 -/
lemma dgGluingCommaForward_primitive_of_zero
    (hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) b g hn) =
    forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega) b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega : q - 1 + p = n - 1) := by
  have he := congrArg (fun a => a
    (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)))
    (Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison R C E F X Y Z)
      n (n - 1) (by omega))
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply] at he
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
    (forward R (x := X) (y := Y) (z := Z) b g hn) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) at he
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.add_v, ModuleCat.hom_add,
    LinearMap.add_apply] at he
  rw [dgGluingCommaFirstPrimitive_element, dgGluingCommaSecondPrimitive_element_zero
      R C E F X Y Z b g hn hg, add_zero] at he
  exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
