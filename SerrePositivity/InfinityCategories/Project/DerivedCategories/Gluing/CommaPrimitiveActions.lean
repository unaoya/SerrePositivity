module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaCompositionElements

/-! 同じ実 comma 合成の第三成分を、両斉次元の二作用と Koszul 符号で完全に記述する。 -/
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

/-- 第二比較項は、先行射の replacement 成分と後続射の第三成分の符号付き合成。 -/
lemma dgGluingCommaSecondPrimitive_element :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) =
    q.negOnePow • forward R (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f q b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g)
      (by omega : q + (p - 1) = n - 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive, cochain_comp_ofHom_apply,
    tensorLeftHom_apply_of_sum _ _ _ (-1) q p n (p - 1) (n - 1) hn (by omega) (by omega)]
  simp only [Units.smul_def, map_zsmul]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    tensorHom_def, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    SerrePositivity.DifferentialGraded.whiskerRight_apply,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply]
  change ((-1) * q).negOnePow •
    forward R (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f q b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g)
      (by omega : q + (p - 1) = n - 1) = _
  simp only [neg_mul, one_mul, Int.negOnePow_neg]
  rfl

/-- 全次数の豊穣順合成の第三成分は、同じ二作用の和。 -/
lemma dgGluingCommaForward_primitive :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) b g hn) =
    forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega) b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega) +
    q.negOnePow • forward R (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f q b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g) (by omega) := by
  have he := congrArg (fun a => a
    (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)))
    (Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison R C E F X Y Z)
      n (n - 1) (by omega))
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, ModuleCat.comp_apply] at he
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
    (forward R (x := X) (y := Y) (z := Z) b g hn) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) at he
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.add_v, ModuleCat.hom_add,
    LinearMap.add_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaFirstPrimitive_element,
    dgGluingCommaSecondPrimitive_element] using he

/-- bottom 成分への後合成では、同じ source 像の作用だけが残る。 -/
lemma dgGluingCommaForward_primitive_of_replacement_zero
    (hb : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f q b = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) b g hn) =
    forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega) b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega) := by
  rw [dgGluingCommaForward_primitive, hb]
  simp only [forward, TensorProduct.zero_tmul, map_zero, smul_zero, add_zero]

/-- bottom 成分への前合成では、同じ replacement 作用と先行次数の符号だけが残る。 -/
lemma dgGluingCommaForward_primitive_of_image_zero
    (hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z).f p g = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) b g hn) =
    q.negOnePow • forward R (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f q b)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g) (by omega) := by
  rw [dgGluingCommaForward_primitive, hg]
  simp only [forward, TensorProduct.tmul_zero, map_zero, zero_add]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
