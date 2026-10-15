module
public import SerrePositivity.DifferentialGraded.Module.Representable

/-! # 固定終域への反変Hom dg関手 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- Ch(A)上の代表右加群を再利用する。対象全体のsmallnessは要求しない。 -/
def homContravariantDG (T : Complex A) : DGFunctor A (Complex A)ᵒᵖ (Complex A) :=
  (representable A T).toFunctor

lemma homContravariantDG_obj (T : Complex A) (P : (Complex A)ᵒᵖ) :
    (homContravariantDG A T).obj P = homComplex A P.unop T := rfl

/-- 反変Homの全次数作用は符号付き前合成。 -/
lemma homContravariantDG_map_element (T : Complex A) (P Q : (Complex A)ᵒᵖ)
    (p q n : ℤ) (hn : q + p = n) (f : Homogeneous Q.unop P.unop p)
    (g : Homogeneous P.unop T q) :
    (((homContravariantDG A T).map P Q).f p f).v q n hn g =
      (p * q).negOnePow • f.comp g (by omega) := by
  change ((representableMap A T P Q).f p f).v q n hn g = _
  rw [representableMap_apply]
  exact enrichedComposition_apply Q.unop P.unop T p q n (by omega) f g

end SerrePositivity.DifferentialGraded
