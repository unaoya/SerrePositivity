module
public import SerrePositivity.InfinityCategories.Derived.Gluing.GradedPostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaProjections

/-! comma の全次数後合成は、実 source・replacement 射影と可換する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F) {p : ℤ}
  (g : (dgFunctorCommaHomComplex R C E F Y Z).X p)
local notation "G" => DGFunctorCommaObject R C E F

/-- source 射影を通すと、同じ source 成分の全次数後合成になる。 -/
lemma dgGluingCommaGradedPost_source :
    ((dgGluingGradedPostcomposition R G X Y Z).f p g).comp
      (Cochain.ofHom (dgFunctorCommaSourceHomMap R C E F X Z)) (add_zero p) =
    (Cochain.ofHom (dgFunctorCommaSourceHomMap R C E F X Y)).comp
      ((dgGluingGradedPostcomposition R C X.source Y.source Z.source).f p
        ((dgFunctorCommaSourceHomMap R C E F Y Z).f p g)) (zero_add p) :=
  dgGluingGradedPostcomposition_naturality R G C (dgFunctorCommaSource R C E F) X Y Z g

/-- replacement 射影も、同じ replacement 成分の全次数後合成を保つ。 -/
lemma dgGluingCommaGradedPost_replacement :
    ((dgGluingGradedPostcomposition R G X Y Z).f p g).comp
      (Cochain.ofHom (dgFunctorCommaReplacementHomMap R C E F X Z)) (add_zero p) =
    (Cochain.ofHom (dgFunctorCommaReplacementHomMap R C E F X Y)).comp
      ((dgGluingGradedPostcomposition R E X.replacement Y.replacement Z.replacement).f p
        ((dgFunctorCommaReplacementHomMap R C E F Y Z).f p g)) (zero_add p) :=
  dgGluingGradedPostcomposition_naturality R G E
    (dgFunctorCommaReplacement R C E F) X Y Z g

end SerrePositivity.InfinityCategories
