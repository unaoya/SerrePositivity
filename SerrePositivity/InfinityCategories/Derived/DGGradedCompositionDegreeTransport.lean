module
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.DGNerve.HomTransport

/-! # 閉前合成と零次数後合成の次数輸送

概要：同じ端点を保つ次数輸送は、閉前合成と零次数後合成に可換である。
方針：前合成では等式を消去し、後合成では一般の線形合成輸送を使う。
規約：合成の出力次数の証明も保持。使われ方：一般二未知式の標準次数からの回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 閉前合成は、同じ端点での次数輸送と可換。 -/
lemma dgGradedPrecompose_degreeTransport {q x y : D} {k l : ℤ} (hkl : k = l)
    (f : GradedHom A x y k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    gradedHomTransport rfl rfl hkl (dgGradedPrecompose A D k f s) =
      dgGradedPrecompose A D l (gradedHomTransport rfl rfl hkl f) s := by
  subst l
  rfl

/-- 零次数射による合成の出力だけを、元の射と同じ次数へ戻す。 -/
lemma dgZeroPostcompose_outputTransport {x y z : D} {k l : ℤ}
    (g : GradedHom A y z 0) (f : GradedHom A x y k) (h : k + 0 = l) (hlk : l = k) :
    gradedHomTransport rfl rfl hlk (compose A g f h) = compose A g f (add_zero k) := by
  have hc := gradedHomTransport_compose (A := A) (D := D) rfl rfl rfl
    (rfl : k = k) (rfl : (0 : ℤ) = 0) hlk g f h
  simp only [gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact hc

end SerrePositivity.InfinityCategories
