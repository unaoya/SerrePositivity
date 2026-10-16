module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # bimoduleの左cochainと左加群作用の成分比較 -/
@[expose] public section
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma leftCochain_apply (M : Bimodule A B C) {c c' : C} {p i n : ℤ}
    (g : GradedHom A c c' p) (b : B) (v : (M.value b c).X i) (hn : i + p = n) :
    (M.leftCochain g b).v i n hn v = leftAction A (M.leftAt b) g v hn := rfl

end SerrePositivity.DifferentialGraded.Bimodule
