module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaCategory
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-! comma 合成の第三 cochain の第一項を、実斉次元の式へ回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F) {p q n : ℤ}
  (b : (dgFunctorCommaHomComplex R C E F X Y).X q)
  (g : (dgFunctorCommaHomComplex R C E F Y Z).X p) (hn : q + p = n)

/-- 第一比較項は、元の比較成分と後続射の像成分の実斉次合成。 -/
lemma dgGluingCommaFirstPrimitive_element :
    (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (dgFunctorCommaHomComplex R C E F X Y)
        (dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) =
    forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      ((dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega) b)
      ((dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega : q - 1 + p = n - 1) := by
  rw [dgFunctorCommaFirstCompositePrimitive, cochain_comp_ofHom_apply,
    tensorRightHom_apply_of_sum _ _ _ (-1) q p n (q - 1) (n - 1) hn (by omega) (by omega)]
  rw [dgFunctorCommaFirstCompositionMap, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    tensorHom_def, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    SerrePositivity.DifferentialGraded.whiskerRight_apply,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply]
  rfl

/-- 後続斉次射の第三成分が零なら、第二比較項の同じ値も零。 -/
lemma dgGluingCommaSecondPrimitive_element_zero
    (hg : (dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g = 0) :
    (dgFunctorCommaSecondCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (dgFunctorCommaHomComplex R C E F X Y)
        (dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) = 0 := by
  rw [dgFunctorCommaSecondCompositePrimitive, cochain_comp_ofHom_apply,
    tensorLeftHom_apply_of_sum _ _ _ (-1) q p n (p - 1) (n - 1) hn (by omega) (by omega)]
  simp only [hg, TensorProduct.tmul_zero, map_zero, smul_zero]

/-- 第三成分零の後続射との合成は、第一比較項だけで元の第三成分を運ぶ。 -/
lemma dgGluingCommaForward_primitive_of_zero
    (hg : (dgFunctorCommaPrimitive R C E F Y Z).v p (p - 1) (by omega) g = 0) :
    (dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) b g hn) =
    forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      ((dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega) b)
      ((dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega : q - 1 + p = n - 1) := by
  have he := congrArg (fun a => a
    (ιTensorObj (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)))
    (Cochain.congr_v (dgFunctorCommaComposition_comparison R C E F X Y Z)
      n (n - 1) (by omega))
  simp only [dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply] at he
  change (dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
    (forward R (x := X) (y := Y) (z := Z) b g hn) =
    (dgFunctorCommaCompositePrimitive R C E F X Y Z).v n (n - 1) (by omega)
      (ιTensorObj (dgFunctorCommaHomComplex R C E F X Y)
        (dgFunctorCommaHomComplex R C E F Y Z) q p n hn (b ⊗ₜ[R] g)) at he
  simp only [dgFunctorCommaCompositePrimitive, Cochain.add_v, ModuleCat.hom_add,
    LinearMap.add_apply] at he
  rw [dgGluingCommaFirstPrimitive_element, dgGluingCommaSecondPrimitive_element_zero
      R C E F X Y Z b g hn hg, add_zero] at he
  exact he

end SerrePositivity.InfinityCategories
