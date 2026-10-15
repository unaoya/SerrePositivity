module
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryHom
public import SerrePositivity.DifferentialGraded.Functor.ComplexValued

/-! # bimoduleの両作用のcochain合成式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite CochainComplex HomComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma rightCochain_forward (M : Bimodule A B C) (c : C) {x y z : Bᵒᵖ} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    ((M.rightAt c).map x z).f n (forward A f g hn) =
      (p * q).negOnePow • (((M.rightAt c).map x y).f p f).comp
        (((M.rightAt c).map y z).f q g) hn :=
  DGFunctor.map_forward_cochain A (M.rightAt c).toFunctor f g hn

lemma leftCochain_forward (M : Bimodule A B C) (b : B) {x y z : C} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    M.leftCochain (forward A f g hn) b =
      (p * q).negOnePow • (M.leftCochain f b).comp (M.leftCochain g b) hn :=
  DGFunctor.map_forward_cochain A (M.leftAt b) f g hn

end SerrePositivity.DifferentialGraded.Bimodule
