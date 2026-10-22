module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaCompositionElements
public import SerrePositivity.InfinityCategories.Derived.Gluing.GradedPostcomposition

/-! 第三成分零の次数 −1 射による通常順合成の、第三成分の負符号。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F) {q : ℤ}
  (b : (dgFunctorCommaHomComplex R C E F X Y).X q)
  (g : (dgFunctorCommaHomComplex R C E F Y Z).X (-1))

/-- 通常順合成に直すと、第三成分は元の第三成分の後合成の負になる。 -/
lemma dgGluingCommaMinusOneCompose_primitive
    (hg : (dgFunctorCommaPrimitive R C E F Y Z).v (-1) (-2) (by omega) g = 0) :
    (dgFunctorCommaPrimitive R C E F X Z).v (q - 1) (q - 1 - 1) (by omega)
      (compose R (x := X) (y := Y) (z := Z) g b (by omega)) =
    -compose R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      ((dgFunctorCommaImageHomMap R C E F Y Z).f (-1) g)
      ((dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega) b) (by omega) := by
  simp only [compose, Units.smul_def, map_zsmul]
  rw [dgGluingCommaForward_primitive_of_zero R C E F X Y Z b g (by omega) hg]
  simp only [Int.negOnePow_neg, Int.negOnePow_sub, Int.negOnePow_one,
    mul_neg, mul_one, Units.val_neg, neg_smul, neg_neg]

/-- 同じ負符号を、全次数の後合成と第三 cochain の合成として回収する。 -/
lemma dgGluingCommaMinusOnePost_primitive
    (hg : (dgFunctorCommaPrimitive R C E F Y Z).v (-1) (-2) (by omega) g = 0) :
    ((dgGluingGradedPostcomposition R (DGFunctorCommaObject R C E F) X Y Z).f (-1) g).comp
      (dgFunctorCommaPrimitive R C E F X Z) (by omega : -1 + -1 = -2) =
    -(dgFunctorCommaPrimitive R C E F X Y).comp
      ((dgGluingGradedPostcomposition R E X.replacement (F.obj Y.source) (F.obj Z.source)).f
        (-1) ((dgFunctorCommaImageHomMap R C E F Y Z).f (-1) g))
      (by omega : -1 + -1 = -2) := by
  apply Cochain.ext
  intro n m hnm
  have hm : m = n - 1 - 1 := by omega
  cases hm
  simp only [Cochain.neg_v]
  rw [Cochain.comp_v _ _ (by omega : -1 + -1 = -2) n (n - 1) (n - 1 - 1)
      (by omega) (by omega),
    Cochain.comp_v _ _ (by omega : -1 + -1 = -2) n (n - 1) (n - 1 - 1)
      (by omega) (by omega)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [ModuleCat.comp_apply, ModuleCat.hom_neg, LinearMap.neg_apply]
  rw [dgGluingGradedPostcomposition_apply, dgGluingGradedPostcomposition_apply]
  exact dgGluingCommaMinusOneCompose_primitive R C E F X Y Z z g hg

end SerrePositivity.InfinityCategories
