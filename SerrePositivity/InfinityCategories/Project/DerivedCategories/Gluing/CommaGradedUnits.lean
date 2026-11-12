module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaCompositionElements

/-! comma の斉次単位と、第三成分零の通常順合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R]

/-- dg 関手は、符号を含む通常順の全次数合成も保存する。 -/
lemma dgGluingFunctor_map_compose {C : Type v} [DGCategory R C]
    {E : Type w} [DGCategory R E] (F : DGFunctor R C E)
    {X Y Z : C} {p q n : ℤ} (g : GradedHom R Y Z q) (f : GradedHom R X Y p)
    (hn : p + q = n) :
    (F.map X Z).f n (compose R g f hn) =
      compose R ((F.map Y Z).f q g) ((F.map X Y).f p f) hn := by
  simp only [compose, Units.smul_def, map_zsmul, F.map_forward R]

variable (C : Type v) [DGCategory R C] (E : Type w) [DGCategory R E]
  (F : DGFunctor R C E)

/-- 同じ実 comma 単位の第三成分は零。 -/
lemma dgGluingCommaUnit_primitive (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X X).v 0 (-1) (by omega)
      (unitElement R X).val = 0 := by
  have h := Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R C E F X)
    0 (-1) (by omega)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.zero_v] at h
  exact congrArg (fun f => f
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv 1)) h

/-- 第三成分零の二元の通常順合成も、第三成分零。 -/
lemma dgGluingCommaCompose_primitive_zero (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
    {p q n : ℤ} (g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z).X q)
    (f : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y).X p) (hn : p + q = n)
    (hf : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v p (p - 1) (by omega) f = 0)
    (hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).v q (q - 1) (by omega) g = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z).v n (n - 1) (by omega)
      (compose R (x := X) (y := Y) (z := Z) g f hn) = 0 := by
  simp only [compose, Units.smul_def, map_zsmul]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaForward_primitive_of_zero R C E F X Y Z f g hn hg, hf]
  simp only [forward, TensorProduct.zero_tmul, map_zero, zsmul_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
