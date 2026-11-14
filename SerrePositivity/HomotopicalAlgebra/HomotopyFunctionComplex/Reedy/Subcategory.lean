module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Degree

/-! # Reedy structures on downward closed full subcategories

Closure under inverse maps is enough to retain the unique normal
factorization. The lower-degree and closed-degree restrictions are examples.
-/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J]

lemma fullSubcategory_identities {P : ObjectProperty J} {x y : P.FullSubcategory}
    (f : x ⟶ y) (hf : MorphismProperty.identities J f.hom) :
    MorphismProperty.identities P.FullSubcategory f := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases f with ⟨f⟩
  cases hf
  exact MorphismProperty.ofHoms.mk _

variable {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (P : ObjectProperty J)

abbrev forgetFactorization {x y : P.FullSubcategory} {f : x ⟶ y}
    (q : MorphismProperty.MapFactorizationData
      (inverse.inverseImage P.ι) (direct.inverseImage P.ι) f) :
    MorphismProperty.MapFactorizationData inverse direct f.hom where
  Z := q.Z.obj
  i := q.i.hom
  p := q.p.hom
  fac := congrArg (fun f ↦ f.hom) q.fac
  hi := q.hi
  hp := q.hp

omit [inverse.IsMultiplicative] [direct.IsMultiplicative] in
lemma forgetFactorization_injective {x y : P.FullSubcategory} (f : x ⟶ y) :
    Function.Injective
      (forgetFactorization (inverse := inverse) (direct := direct) P (f := f)) := by
  rintro ⟨⟨Z, hZ⟩, ⟨i⟩, ⟨p⟩, h, hi, hp⟩ ⟨⟨Z', hZ'⟩, ⟨i'⟩, ⟨p'⟩, h', hi', hp'⟩ hq
  change (MorphismProperty.MapFactorizationData.mk Z i p _ hi hp) =
    (MorphismProperty.MapFactorizationData.mk Z' i' p' _ hi' hp') at hq
  cases hq
  rfl

variable (hP : ∀ {x y : J} (f : x ⟶ y), inverse f → P x → P y)

def subFactorization {x y : P.FullSubcategory} (f : x ⟶ y) :
    MorphismProperty.MapFactorizationData
      (inverse.inverseImage P.ι) (direct.inverseImage P.ι) f where
  Z := ⟨(r.mapFactorizationData f.hom).Z,
    hP _ (r.mapFactorizationData f.hom).hi x.property⟩
  i := ObjectProperty.homMk (r.mapFactorizationData f.hom).i
  p := ObjectProperty.homMk (r.mapFactorizationData f.hom).p
  fac := by
    apply ObjectProperty.hom_ext
    exact (r.mapFactorizationData f.hom).fac
  hi := (r.mapFactorizationData f.hom).hi
  hp := (r.mapFactorizationData f.hom).hp

def fullSubcategory : ReedyStructure (inverse.inverseImage P.ι) (direct.inverseImage P.ι) α where
  deg x := r.deg x.obj
  lt₁ f hf hf' := r.lt₁ f.hom hf (fun h ↦ hf' (fullSubcategory_identities f h))
  lt₂ f hf hf' := r.lt₂ f.hom hf (fun h ↦ hf' (fullSubcategory_identities f h))
  nonempty_unique f := by
    have := r.subsingleton_mapFactorizationData f.hom
    have : Subsingleton (MorphismProperty.MapFactorizationData
        (inverse.inverseImage P.ι) (direct.inverseImage P.ι) f) :=
      (forgetFactorization_injective (inverse := inverse) (direct := direct) P f).subsingleton
    exact ⟨{ default := subFactorization r P hP f, uniq := fun _ ↦ Subsingleton.elim _ _ }⟩

abbrev lowerReedy (a : α) : ReedyStructure
    (inverse.inverseImage (lowerInclusion r a)) (direct.inverseImage (lowerInclusion r a)) α :=
  fullSubcategory r (lowerProperty r a) (fun f hf hx ↦ lt_of_le_of_lt (r.le₁ f hf) hx)

abbrev upperProperty (a : α) : ObjectProperty J := fun j ↦ r.deg j ≤ a
abbrev Upper (a : α) := (upperProperty r a).FullSubcategory
abbrev upperInclusion (a : α) : Upper r a ⥤ J := (upperProperty r a).ι

abbrev upperReedy (a : α) : ReedyStructure
    (inverse.inverseImage (upperInclusion r a)) (direct.inverseImage (upperInclusion r a)) α :=
  fullSubcategory r (upperProperty r a) (fun f hf hx ↦ (r.le₁ f hf).trans hx)

end SerrePositivity.Reedy

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.9.13" (partial := special) "仮定：整列次数を指定し、部分圏をその下方または閉切断に限定（Lean が強い特殊形）。結論：射類を制限した実際の ReedyStructure を構成する。この下方閉部分圏について原典の結論に一致するが、任意の good filtration に対する主張ではない。"] _root_.SerrePositivity.Reedy.lowerReedy
attribute [cite HTT "A.2.9.13" (partial := special) "仮定：整列次数を指定し、部分圏をその下方または閉切断に限定（Lean が強い特殊形）。結論：射類を制限した実際の ReedyStructure を構成する。この下方閉部分圏について原典の結論に一致するが、任意の good filtration に対する主張ではない。"] _root_.SerrePositivity.Reedy.upperReedy
