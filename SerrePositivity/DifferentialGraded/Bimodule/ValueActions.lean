module
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.HomNaturalityEvaluation

/-! # 閉零bimodule射の値成分と左右斉次作用の可換式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma valueMap_leftAction {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (b : B) (c c' : C) {p i n : ℤ} (hn : i + p = n) (g : GradedHom A c c' p)
    (v : ((underlying A B C M).value b c).X i) :
    ((valueEvaluation A B C b c').map a).f n
      (leftAction A ((underlying A B C M).leftAt b) g v hn) =
    leftAction A ((underlying A B C N).leftAt b) g
      (((valueEvaluation A B C b c).map a).f i v) hn :=
  hom_naturality_apply (((underlying A B C M).leftAt b).map c c')
    (((underlying A B C N).leftAt b).map c c')
    ((valueEvaluation A B C b c).map a) ((valueEvaluation A B C b c').map a)
    (valueMap_left_naturality A B C a b c c') hn g v

lemma valueMap_rightAction {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (b b' : Bᵒᵖ) (c : C) {p i n : ℤ} (hn : i + p = n) (g : GradedHom A b b' p)
    (v : ((underlying A B C M).value b.unop c).X i) :
    ((valueEvaluation A B C b'.unop c).map a).f n
      (moduleAction A ((underlying A B C M).rightAt c) g v hn) =
    moduleAction A ((underlying A B C N).rightAt c) g
      (((valueEvaluation A B C b.unop c).map a).f i v) hn := by
  let τ := moduleClosedHomEquiv A B ((evaluation A B C c).obj M)
    ((evaluation A B C c).obj N) ((evaluation A B C c).map a)
  exact closedFamily_action A (closedTransApp A τ) (closedTransApp_naturality A τ)
    b b' p i n hn g v

end SerrePositivity.DifferentialGraded.BimoduleCategory
