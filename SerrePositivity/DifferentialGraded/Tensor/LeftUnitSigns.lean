module
public import SerrePositivity.DifferentialGraded.Module.Yoneda

/-! # 左単位比較に現れる作用のKoszul符号 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B]

/-- 左因子を越える符号と左Yoneda評価の符号が作用の結合則と整合する。 -/
lemma moduleAction_signed_representable (M : RightModule A B) (b b' x : B)
    (p r s a n : ℤ) (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (h : GradedHom A b x s)
    (m : (M.obj (op x)).X r) :
    (p * r).negOnePow • ((r * (p + s)).negOnePow •
      moduleAction A M (x := op x) (y := op b')
        (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega)) m (by omega)) =
    (r * s).negOnePow • moduleAction A M f (moduleAction A M h m ha) hn := by
  have hc := moduleAction_representable A x M (op b) (op b') p s r (p + s) n a
    (by omega) ha (by omega) f h m
  change moduleAction A M (x := op x) (y := op b')
    (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega)) m (by omega) =
      _ at hc
  rw [hc]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : p * r + r * (p + s) = r * s + 2 * (p * r) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity.DifferentialGraded
