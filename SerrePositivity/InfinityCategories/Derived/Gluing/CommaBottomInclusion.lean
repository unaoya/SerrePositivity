module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeBottomComponents
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaComparison

/-! comma の同じ Hom 複体への標準 bottom 包含と、その全次数の三成分。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F)

def dgGluingCommaBottomInclusion :
    (homObject R E X.replacement (F.obj Y.source))⟦(-1 : ℤ)⟧ ⟶
      dgFunctorCommaHomComplex R C E F X Y :=
  dgGluingCoconeBottomInclusion (dgFunctorCommaDifference R C E F X Y)

lemma dgGluingCommaBottomInclusion_source :
    dgGluingCommaBottomInclusion R C E F X Y ≫
      dgFunctorCommaSourceHomMap R C E F X Y = 0 := by
  simp only [dgGluingCommaBottomInclusion, dgFunctorCommaSourceHomMap,
    ← Category.assoc, dgGluingCoconeBottomInclusion_fst, zero_comp]

lemma dgGluingCommaBottomInclusion_replacement :
    dgGluingCommaBottomInclusion R C E F X Y ≫
      dgFunctorCommaReplacementHomMap R C E F X Y = 0 := by
  simp only [dgGluingCommaBottomInclusion, dgFunctorCommaReplacementHomMap,
    ← Category.assoc, dgGluingCoconeBottomInclusion_fst, zero_comp]

lemma dgGluingCommaBottomInclusion_primitive (n : ℤ) :
    (dgGluingCommaBottomInclusion R C E F X Y).f n ≫
      (dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega) = 𝟙 _ :=
  dgGluingCoconeBottomInclusion_snd _ n

end SerrePositivity.InfinityCategories
