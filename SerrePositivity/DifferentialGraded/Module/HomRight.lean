module
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import SerrePositivity.DifferentialGraded.Complexes.HomContravariant

/-! # 左dg加群から固定終域への右Hom加群 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 値がHom_A(N(x),T)である右dg加群。NのoppositeとCh(A)の代表加群の合成。 -/
def homRightModule (N : LeftModule A D) (T : Complex A) : RightModule A D :=
  N.op.comp (homContravariantDG A T)

lemma homRightModule_obj (N : LeftModule A D) (T : Complex A) (x : Dᵒᵖ) :
    (homRightModule A D N T).obj x = homComplex A (N.obj x.unop) T := rfl

/-- 任意次数の作用はNの作用による符号付き前合成である。 -/
lemma homRightModule_action (N : LeftModule A D) (T : Complex A) (x y : Dᵒᵖ)
    (p q n : ℤ) (hn : q + p = n) (f : GradedHom A x y p)
    (g : Homogeneous (N.obj x.unop) T q) :
    (((homRightModule A D N T).map x y).f p f).v q n hn g =
    (p * q).negOnePow • (((N.map y.unop x.unop).f p f).comp g (by omega)) := by
  change (((homContravariantDG A T).map (op (N.obj x.unop))
      (op (N.obj y.unop))).f p ((N.map y.unop x.unop).f p f)).v q n hn g = _
  exact homContravariantDG_map_element A T (op (N.obj x.unop)) (op (N.obj y.unop))
    p q n hn ((N.map y.unop x.unop).f p f) g

end SerrePositivity.DifferentialGraded
