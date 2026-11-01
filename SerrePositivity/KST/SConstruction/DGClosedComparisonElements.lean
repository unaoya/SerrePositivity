module
public import SerrePositivity.KST.SConstruction.DGClosedWhiskerComponents
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedNaturality

/-! # 全 Hom 自然な閉比較の整数次数ごとの合成式
概要：元の閉比較の全 Hom 自然性を、各斉次元の前後合成の等号へ移す。
方針：閉零射の豊穣前後合成の成分を評価し、零次数の符号を消す。
規約：全整数次数を保持。使われ方：Hom 双加群の閉比較族。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {P : Type v} [DGCategory R P]
  {E : Type w} [DGCategory R E] (F G : DGFunctor R P E)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)))

include h in
/-- 元の閉比較と全次数 Hom 射の前後合成は、同じ標的内で厳密に一致する。 -/
lemma dgClosedComparison_forward (x y : P) (n : ℤ) (f : GradedHom R x y n) :
    forward R (closedHomEquiv R E _ _ (a x)).val ((G.map x y).f n f) (zero_add n) =
      forward R ((F.map x y).f n f) (closedHomEquiv R E _ _ (a y)).val (add_zero n) := by
  have he := congrArg (fun k => k.f n f) (h x y)
  change (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x))
    (a y)).f n ((F.map x y).f n f) =
    (eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y))).f n ((G.map x y).f n f) at he
  rw [dgClosedWhiskerLeft_f, dgClosedWhiskerRight_f] at he
  simp only [compose, mul_zero, zero_mul, Int.negOnePow_zero, one_smul] at he
  exact he.symm

end SerrePositivity.KST.SConstruction
