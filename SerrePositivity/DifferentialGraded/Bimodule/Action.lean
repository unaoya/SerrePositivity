module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # bimoduleの斉次二作用とKoszul交換則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite CochainComplex HomComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右B作用。 -/
def actRight (M : Bimodule A B C) {b b' : B} {c : C} {p r n : ℤ}
    (f : GradedHom A (op b') (op b) p) (v : (M.value b' c).X r)
    (hn : r + p = n) : (M.value b c).X n :=
  moduleAction A (M.rightAt c) f v hn

/-- 左C作用。 -/
def actLeft (M : Bimodule A B C) {b : B} {c c' : C} {q r n : ℤ}
    (g : GradedHom A c c' q) (v : (M.value b c).X r)
    (hn : r + q = n) : (M.value b c').X n :=
  (M.leftCochain g b).v r n hn v

/-- 左右の作用を交換すると次数積のKoszul符号を得る。 -/
lemma act_interchange (M : Bimodule A B C) {b b' : B} {c c' : C} {p q r n : ℤ}
    (f : GradedHom A (op b') (op b) p) (g : GradedHom A c c' q)
    (v : (M.value b' c).X r) (hn : r + (q + p) = n) :
    M.actLeft (n := n) g (M.actRight f v rfl) (by omega) =
      (q * p).negOnePow • M.actRight (n := n) f (M.actLeft g v rfl) (by omega) := by
  have h := congrArg (fun h => h.v r n hn v) (M.interchange f g)
  rw [Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ rfl r (r + q) n rfl (by omega)] at h
  exact h

lemma actRight_unit (M : Bimodule A B C) (b : B) (c : C) (r : ℤ)
    (v : (M.value b c).X r) :
    M.actRight (unitElement A (op b)).val v (add_zero r) = v :=
  moduleAction_unit A (M.rightAt c) (op b) r v

lemma actLeft_unit (M : Bimodule A B C) (b : B) (c : C) (r : ℤ)
    (v : (M.value b c).X r) :
    M.actLeft (unitElement A c).val v (add_zero r) = v := by
  change leftAction A (M.leftAt b) (unitElement A c).val v (add_zero r) = v
  exact leftAction_unit A (M.leftAt b) c r v

end SerrePositivity.DifferentialGraded.Bimodule
