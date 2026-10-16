module
public import SerrePositivity.DifferentialGraded.Bimodule.ActionEvaluation

/-! # 値の複体を始域・終域に固定したbimoduleの斉次左作用 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左加群への変換を型に含めず、全Hom cochainから左作用を評価する。 -/
@[irreducible]
def leftActionElement (M : Bimodule A B C) {c c' : C} {p i n : ℤ}
    (g : GradedHom A c c' p) (b : B) (v : (M.value b c).X i) (hn : i + p = n) :
    (M.value b c').X n :=
  (M.leftCochain g b).v i n hn v

lemma leftActionElement_eq (M : Bimodule A B C) {c c' : C} {p i n : ℤ}
    (g : GradedHom A c c' p) (b : B) (v : (M.value b c).X i) (hn : i + p = n) :
    leftActionElement A M g b v hn = leftAction A (M.leftAt b) g v hn := by
  unfold leftActionElement
  exact leftCochain_apply A B C M g b v hn

end SerrePositivity.DifferentialGraded.Bimodule
