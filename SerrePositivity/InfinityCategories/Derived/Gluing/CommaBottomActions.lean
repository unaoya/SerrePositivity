module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaBottomInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrimitiveActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaElementExt
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaProjections

/-! 標準 bottom 包含は、全次数の前後合成に関して同じ符号付き作用を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F) {q : ℤ}

lemma dgGluingCommaBottomInclusion_source_apply
    (t : ((homObject R E X.replacement (F.obj Y.source))⟦(-1 : ℤ)⟧).X q) :
    (dgFunctorCommaSourceHomMap R C E F X Y).f q
      ((dgGluingCommaBottomInclusion R C E F X Y).f q t) = 0 := by
  have h := congrArg (fun k => k.f q t)
    (dgGluingCommaBottomInclusion_source R C E F X Y)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h

lemma dgGluingCommaBottomInclusion_replacement_apply
    (t : ((homObject R E X.replacement (F.obj Y.source))⟦(-1 : ℤ)⟧).X q) :
    (dgFunctorCommaReplacementHomMap R C E F X Y).f q
      ((dgGluingCommaBottomInclusion R C E F X Y).f q t) = 0 := by
  have h := congrArg (fun k => k.f q t)
    (dgGluingCommaBottomInclusion_replacement R C E F X Y)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h

lemma dgGluingCommaBottomInclusion_primitive_apply
    (t : ((homObject R E X.replacement (F.obj Y.source))⟦(-1 : ℤ)⟧).X q) :
    (dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega)
      ((dgGluingCommaBottomInclusion R C E F X Y).f q t) = t := by
  have h := congrArg (fun k => k t)
    (dgGluingCommaBottomInclusion_primitive R C E F X Y q)
  change (dgFunctorCommaPrimitive R C E F X Y).v q (q - 1) (by omega)
    ((dgGluingCommaBottomInclusion R C E F X Y).f q t) = t at h
  exact h

variable {p n : ℤ} (hn : q + p = n)

/-- 後合成は像側の作用であり、追加の次数符号を持たない。 -/
lemma dgGluingCommaBottom_forward
    (t : ((homObject R E X.replacement (F.obj Y.source))⟦(-1 : ℤ)⟧).X q)
    (g : (dgFunctorCommaHomComplex R C E F Y Z).X p) :
    forward R (x := X) (y := Y) (z := Z) (p := q) (q := p) (n := n)
      ((dgGluingCommaBottomInclusion R C E F X Y).f q t) g hn =
    (dgGluingCommaBottomInclusion R C E F X Z).f n
      (forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
        (p := q - 1) (q := p) (n := n - 1)
        t ((dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega)) := by
  apply dgGluingCommaElement_ext R C E F X Z n
  · have hm := DGFunctor.map_forward R (dgFunctorCommaSource R C E F)
      (x := X) (y := Y) (z := Z) (p := q) (q := p) (n := n)
      ((dgGluingCommaBottomInclusion R C E F X Y).f q t) g hn
    dsimp only [dgFunctorCommaSource] at hm
    refine hm.trans ?_
    change forward R (x := X.source) (y := Y.source) (z := Z.source)
      ((dgFunctorCommaSourceHomMap R C E F X Y).f q
        ((dgGluingCommaBottomInclusion R C E F X Y).f q t))
      ((dgFunctorCommaSourceHomMap R C E F Y Z).f p g) hn = _
    rw [dgGluingCommaBottomInclusion_source_apply R C E F X Z (q := n),
      dgGluingCommaBottomInclusion_source_apply R C E F X Y (q := q) t]
    simp only [forward, TensorProduct.zero_tmul, map_zero]
  · have hm := DGFunctor.map_forward R (dgFunctorCommaReplacement R C E F)
      (x := X) (y := Y) (z := Z) (p := q) (q := p) (n := n)
      ((dgGluingCommaBottomInclusion R C E F X Y).f q t) g hn
    dsimp only [dgFunctorCommaReplacement] at hm
    refine hm.trans ?_
    change forward R (x := X.replacement) (y := Y.replacement) (z := Z.replacement)
      ((dgFunctorCommaReplacementHomMap R C E F X Y).f q
        ((dgGluingCommaBottomInclusion R C E F X Y).f q t))
      ((dgFunctorCommaReplacementHomMap R C E F Y Z).f p g) hn = _
    rw [dgGluingCommaBottomInclusion_replacement_apply R C E F X Z (q := n),
      dgGluingCommaBottomInclusion_replacement_apply R C E F X Y (q := q) t]
    simp only [forward, TensorProduct.zero_tmul, map_zero]
  · have he := dgGluingCommaForward_primitive_of_replacement_zero R C E F X Y Z
      (p := p) (q := q) (n := n)
      ((dgGluingCommaBottomInclusion R C E F X Y).f q t) g hn
      (dgGluingCommaBottomInclusion_replacement_apply R C E F X Y (q := q) t)
    have ht := dgGluingCommaBottomInclusion_primitive_apply R C E F X Y (q := q) t
    have hw := dgGluingCommaBottomInclusion_primitive_apply R C E F X Z (q := n)
      (forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
        (p := q - 1) (q := p) (n := n - 1) t
        ((dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega))
    exact he.trans ((congrArg (fun a : GradedHom R X.replacement (F.obj Y.source) (q - 1) =>
      forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
        (p := q - 1) (q := p) (n := n - 1) a
        ((dgFunctorCommaImageHomMap R C E F Y Z).f p g) (by omega)) ht).trans hw.symm)

/-- 前合成は replacement 側の作用であり、先行次数の符号を持つ。 -/
lemma dgGluingComma_forward_bottom
    (b : (dgFunctorCommaHomComplex R C E F X Y).X q)
    (t : ((homObject R E Y.replacement (F.obj Z.source))⟦(-1 : ℤ)⟧).X p) :
    forward R (x := X) (y := Y) (z := Z) (p := q) (q := p) (n := n)
      b ((dgGluingCommaBottomInclusion R C E F Y Z).f p t) hn =
    (dgGluingCommaBottomInclusion R C E F X Z).f n
      (q.negOnePow • forward R
        (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
        (p := q) (q := p - 1) (n := n - 1)
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f q b) t (by omega)) := by
  apply dgGluingCommaElement_ext R C E F X Z n
  · have hm := DGFunctor.map_forward R (dgFunctorCommaSource R C E F)
      (x := X) (y := Y) (z := Z) (p := q) (q := p) (n := n)
      b ((dgGluingCommaBottomInclusion R C E F Y Z).f p t) hn
    dsimp only [dgFunctorCommaSource] at hm
    refine hm.trans ?_
    change forward R (x := X.source) (y := Y.source) (z := Z.source)
      ((dgFunctorCommaSourceHomMap R C E F X Y).f q b)
      ((dgFunctorCommaSourceHomMap R C E F Y Z).f p
        ((dgGluingCommaBottomInclusion R C E F Y Z).f p t)) hn = _
    rw [dgGluingCommaBottomInclusion_source_apply R C E F X Z (q := n),
      dgGluingCommaBottomInclusion_source_apply R C E F Y Z (q := p) t]
    simp only [forward, TensorProduct.tmul_zero, map_zero]
  · have hm := DGFunctor.map_forward R (dgFunctorCommaReplacement R C E F)
      (x := X) (y := Y) (z := Z) (p := q) (q := p) (n := n)
      b ((dgGluingCommaBottomInclusion R C E F Y Z).f p t) hn
    dsimp only [dgFunctorCommaReplacement] at hm
    refine hm.trans ?_
    change forward R (x := X.replacement) (y := Y.replacement) (z := Z.replacement)
      ((dgFunctorCommaReplacementHomMap R C E F X Y).f q b)
      ((dgFunctorCommaReplacementHomMap R C E F Y Z).f p
        ((dgGluingCommaBottomInclusion R C E F Y Z).f p t)) hn = _
    rw [dgGluingCommaBottomInclusion_replacement_apply R C E F X Z (q := n),
      dgGluingCommaBottomInclusion_replacement_apply R C E F Y Z (q := p) t]
    simp only [forward, TensorProduct.tmul_zero, map_zero]
  · have hz : (dgFunctorCommaImageHomMap R C E F Y Z).f p
        ((dgGluingCommaBottomInclusion R C E F Y Z).f p t) = 0 := by
      change (F.map Y.source Z.source).f p
        ((dgFunctorCommaSourceHomMap R C E F Y Z).f p
          ((dgGluingCommaBottomInclusion R C E F Y Z).f p t)) = 0
      rw [dgGluingCommaBottomInclusion_source_apply R C E F Y Z (q := p) t, map_zero]
    have he := dgGluingCommaForward_primitive_of_image_zero R C E F X Y Z
      (p := p) (q := q) (n := n) b
      ((dgGluingCommaBottomInclusion R C E F Y Z).f p t) hn hz
    have ht := dgGluingCommaBottomInclusion_primitive_apply R C E F Y Z (q := p) t
    have hw := dgGluingCommaBottomInclusion_primitive_apply R C E F X Z (q := n)
      (q.negOnePow • forward R
        (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
        (p := q) (q := p - 1) (n := n - 1)
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f q b) t (by omega))
    exact he.trans ((congrArg (fun a : GradedHom R Y.replacement (F.obj Z.source) (p - 1) =>
      q.negOnePow • forward R
        (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
        (p := q) (q := p - 1) (n := n - 1)
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f q b) a (by omega)) ht).trans hw.symm)

end SerrePositivity.InfinityCategories
