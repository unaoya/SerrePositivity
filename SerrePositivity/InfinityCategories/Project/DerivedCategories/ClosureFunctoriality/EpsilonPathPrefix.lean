module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.EpsilonTensorRetraction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.QuotientWordSeparation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellUnitNonzero
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：任意長の語への ε 前置と、その次数別係数回収。
方針：path の生成式と tensor の単位係数射影を合成する。
規約：元 Hom の空語だけでなく、任意の有限収縮語の項を扱う。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded DGQuotient
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set D) (x : S) (y : D)

/-- 任意長の語への ε 左合成は、その語の先頭に同じ収縮対象を加える。 -/
lemma epsilon_word_left (w : Word S) (q : ℤ) (t : (term R D w x.val y).X q) :
    forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
      (epsilonElement R D S x) ((ι R D S x.val y w).f q t) rfl =
    (ι R D S x.val y (x :: w)).f ((-1) + q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft R (homObject R D x.val x.val) (term R D w x.val y)
        q (unitElement R x.val).val t) := by
  have h := path_inclusion_generator R D x w x.val y 0 q ((-1) + q)
    (zero_add _) (unitElement R x.val).val t
  have hu : (originalHomInclusion R D S x.val x.val).f 0 (unitElement R x.val).val =
      (unitElement R (⟨x.val⟩ : QuotientObject D S)).val :=
    (inclusion R D S).map_unitElement R x.val
  let z : GradedHom R (⟨x.val⟩ : QuotientObject D S) ⟨y⟩ ((-1) + q) :=
    forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
      (epsilonElement R D S x) ((ι R D S x.val y w).f q t) rfl
  have hh := congrArg (fun a : GradedHom R (⟨x.val⟩ : QuotientObject D S) ⟨x.val⟩ 0 =>
    forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
      a z (zero_add _)) hu
  exact (hh.trans (forward_unit R (D := QuotientObject D S) z)).symm.trans h.symm

/-- 前置された指定語の成分から、ε と先頭単位を除いて元の項を回収する次数別射。 -/
def epsilonWordLeftRetraction (w : Word S) (q : ℤ)
    (l : (homObject R D x.val x.val).X 0 →ₗ[R] R) :
    (internalHom R D S x.val y).X ((-1) + q) ⟶ (term R D w x.val y).X q :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientWordProjection R D S x.val y (x :: w)).f ((-1) + q) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeftRetraction R (homObject R D x.val x.val) (term R D w x.val y) q l

/-- 任意の一語の項に対し、ε 前置後の係数回収は厳密な左逆となる。 -/
lemma epsilonWordLeftRetraction_apply (w : Word S) (q : ℤ)
    (l : (homObject R D x.val x.val).X 0 →ₗ[R] R)
    (hl : l (unitElement R x.val).val = 1) (t : (term R D w x.val y).X q) :
    epsilonWordLeftRetraction R D S x y w q l
      (forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
        (epsilonElement R D S x) ((ι R D S x.val y w).f q t) rfl) = t := by
  rw [epsilon_word_left]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f ((-1) + q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientWordProjection_split R D S x.val y (x :: w)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft R (homObject R D x.val x.val) (term R D w x.val y)
      q (unitElement R x.val).val t)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply] at h
  simp only [epsilonWordLeftRetraction, ModuleCat.comp_apply]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientWordProjection R D S x.val y (x :: w)).f ((-1) + q)
    ((ι R D S x.val y (x :: w)).f ((-1) + q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft R (homObject R D x.val x.val) (term R D w x.val y)
        q (unitElement R x.val).val t)) = _ at h
  exact (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeftRetraction R
    (homObject R D x.val x.val) (term R D w x.val y) q l z) h).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeftRetraction_apply R _ _ q l _ hl t)

/-- ε 左合成を、全ての語を含む商 Hom の次数別加群射として保持する。 -/
def epsilonLeftComposition (q : ℤ) :
    (internalHom R D S x.val y).X q ⟶ (internalHom R D S x.val y).X ((-1) + q) :=
  ModuleCat.ofHom
    (((eComp (Complex R) (⟨x.val⟩ : QuotientObject D S) ⟨x.val⟩ ⟨y⟩).f ((-1) + q)).hom.comp
      ((ιTensorObj (homObject R (QuotientObject D S) ⟨x.val⟩ ⟨x.val⟩)
        (homObject R (QuotientObject D S) ⟨x.val⟩ ⟨y⟩) (-1) q ((-1) + q) rfl).hom.comp
          (TensorProduct.mk R _ _ (epsilonElement R D S x))))

/-- 各語の ε 除去成分。指定した先頭対象と一致する語だけを読む。 -/
def epsilonLeftRetractionComponent (q : ℤ)
    (l : (homObject R D x.val x.val).X 0 →ₗ[R] R) (w : Word S) :
    (term R D w x.val y).X ((-1) + q) ⟶ (internalHom R D S x.val y).X q := by
  classical
  cases w with
  | nil => exact 0
  | cons b w =>
    by_cases h : b = x
    · subst b
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeftRetraction R (homObject R D x.val x.val)
        (term R D w x.val y) q l ≫ (ι R D S x.val y w).f q
    · exact 0

/-- 全語の成分に対し、指定先頭 ε を除去して元の直和へ戻す次数別射。 -/
def epsilonLeftRetraction (q : ℤ)
    (l : (homObject R D x.val x.val).X 0 →ₗ[R] R) :
    (internalHom R D S x.val y).X ((-1) + q) ⟶ (internalHom R D S x.val y).X q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientDegreeDesc R D S x.val y ((-1) + q) ((internalHom R D S x.val y).X q)
    (epsilonLeftRetractionComponent R D S x y q l)

/-- 任意の語の包含上で、全語の ε 除去射は元の項を回収する。 -/
lemma epsilonLeftRetraction_word (q : ℤ)
    (l : (homObject R D x.val x.val).X 0 →ₗ[R] R)
    (hl : l (unitElement R x.val).val = 1)
    (w : Word S) (t : (term R D w x.val y).X q) :
    epsilonLeftRetraction R D S x y q l
      (epsilonLeftComposition R D S x y q ((ι R D S x.val y w).f q t)) =
        (ι R D S x.val y w).f q t := by
  classical
  change epsilonLeftRetraction R D S x y q l
    (forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
      (epsilonElement R D S x) ((ι R D S x.val y w).f q t) rfl) = _
  rw [epsilon_word_left]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientDegreeDesc_ι R D S x.val y ((-1) + q)
    ((internalHom R D S x.val y).X q)
    (epsilonLeftRetractionComponent R D S x y q l) (x :: w)
  change (ι R D S x.val y (x :: w)).f ((-1) + q) ≫
    epsilonLeftRetraction R D S x y q l = _ at h
  have ht := ConcreteCategory.congr_hom h
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft R (homObject R D x.val x.val) (term R D w x.val y)
      q (unitElement R x.val).val t)
  simpa [epsilonLeftRetractionComponent, ModuleCat.comp_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeftRetraction_apply R _ _ q l _ hl t] using ht

/-- 任意の有限和を含む全商 Hom 上で、ε 左合成には次数別左逆がある。 -/
lemma epsilonLeftComposition_retraction (q : ℤ)
    (l : (homObject R D x.val x.val).X 0 →ₗ[R] R)
    (hl : l (unitElement R x.val).val = 1) :
    epsilonLeftComposition R D S x y q ≫ epsilonLeftRetraction R D S x y q l = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientDegreeHom_ext R D S x.val y q
  intro w
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact epsilonLeftRetraction_word R D S x y q l hl w t

/-- 全商 Hom での ε 左合成は、次数ごとに単射。 -/
lemma epsilonLeftComposition_injective (q : ℤ)
    (l : (homObject R D x.val x.val).X 0 →ₗ[R] R)
    (hl : l (unitElement R x.val).val = 1) :
    Function.Injective (epsilonLeftComposition R D S x y q) := by
  intro a b hab
  have ha := ConcreteCategory.congr_hom (epsilonLeftComposition_retraction R D S x y q l hl) a
  have hb := ConcreteCategory.congr_hom (epsilonLeftComposition_retraction R D S x y q l hl) b
  change epsilonLeftRetraction R D S x y q l (epsilonLeftComposition R D S x y q a) = a at ha
  change epsilonLeftRetraction R D S x y q l (epsilonLeftComposition R D S x y q b) = b at hb
  exact ha.symm.trans ((congrArg (epsilonLeftRetraction R D S x y q l) hab).trans hb)

/-- 標準 cell 分解の実商では、各指定 ε の左合成は全次数で単射となる。 -/
lemma epsilonCellLeftComposition_injective
    (T : Set (DGCategoryCellResolution.Source R D))
    (b : T) (z : DGCategoryCellResolution.Source R D) (q : ℤ) :
    Function.Injective
      (epsilonLeftComposition R (DGCategoryCellResolution.Source R D) T b z q) :=
  epsilonLeftComposition_injective R (DGCategoryCellResolution.Source R D) T b z q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellUnitScalar R D b.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellUnitScalar_unit R D b.val)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
