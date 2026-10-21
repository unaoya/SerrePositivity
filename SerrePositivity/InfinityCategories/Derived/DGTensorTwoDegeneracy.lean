module
public import SerrePositivity.InfinityCategories.Derived.DGTensorLowSimplex
/-!
概要：二つの実一単体を退化させた tensor 二単体は、同じ実 tensor 一単体の退化に一致。
方針：三辺の閉射を実単位で照合し、同じ比較 cochain の両零項を消す。
規約：0〜2次元の面・退化整合性。全次元の自然性を結論しない。
使われ方：dg nerve の実 tensor 写像の低次部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 実三辺と同じ比較 cochain を照合して、三角形データまたは実退化の等式を得る。 -/
lemma dgTriangleData_ext {E : Type v} [DGCategory R E]
    (s t : TriangleData R E) (ho : s.obj = t.obj)
    (h01 : HEq s.f01 t.f01) (h12 : HEq s.f12 t.f12) (h02 : HEq s.f02 t.f02)
    (hh : HEq s.homotopy t.homotopy) : s = t := by
  rcases s with ⟨so, s01, s12, s02, sh, sd⟩
  rcases t with ⟨tobj, t01, t12, t02, th, td⟩
  cases ho
  cases eq_of_heq h01
  cases eq_of_heq h12
  cases eq_of_heq h02
  cases eq_of_heq hh
  rfl
/-- 実三辺と同じ比較 cochain を照合して、三角形データまたは実退化の等式を得る。 -/
lemma dgTensorTwoSimplex_sigma0 (s : Simplex R B 1) (t : Simplex R C 1) :
    dgTensorTwoSimplex R B C ((dgNerve R B).σ 0 s) ((dgNerve R C).σ 0 t) =
      (dgNerve R (DGTensorCategory R B C)).σ 0 (dgTensorOneSimplex R B C s t) := by
  apply Simplex.triangleEquiv.injective
  apply dgTriangleData_ext R
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    simpa only using! (dgTensor_unitElement R B C (s.obj 0, t.obj 0)).symm
  · apply heq_of_eq
    apply Subtype.ext
    rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl
  · apply heq_of_eq
    change dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
      (y := ((s.obj 1, t.obj 1) : DGTensorCategory R B C))
      (p := -1) (q := 0) (n := -1) 0 _ (by decide) +
      dgTensorElement R
        (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
        (y := ((s.obj 1, t.obj 1) : DGTensorCategory R B C))
        (p := 0) (q := -1) (n := -1) _ 0 (by decide) = 0
    rw [dgTensorElement_zero_left, dgTensorElement_zero_right, add_zero]
/-- 実三辺と同じ比較 cochain を照合して、三角形データまたは実退化の等式を得る。 -/
lemma dgTensorTwoSimplex_sigma1 (s : Simplex R B 1) (t : Simplex R C 1) :
    dgTensorTwoSimplex R B C ((dgNerve R B).σ 1 s) ((dgNerve R C).σ 1 t) =
      (dgNerve R (DGTensorCategory R B C)).σ 1 (dgTensorOneSimplex R B C s t) := by
  apply Simplex.triangleEquiv.injective
  apply dgTriangleData_ext R
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl
  · apply heq_of_eq
    apply Subtype.ext
    simpa only using! (dgTensor_unitElement R B C (s.obj 1, t.obj 1)).symm
  · apply heq_of_eq
    apply Subtype.ext
    rfl
  · apply heq_of_eq
    change dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
      (y := ((s.obj 1, t.obj 1) : DGTensorCategory R B C))
      (p := -1) (q := 0) (n := -1) 0 _ (by decide) +
      dgTensorElement R
        (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
        (y := ((s.obj 1, t.obj 1) : DGTensorCategory R B C))
        (p := 0) (q := -1) (n := -1) _ 0 (by decide) = 0
    rw [dgTensorElement_zero_left, dgTensorElement_zero_right, add_zero]
end SerrePositivity.InfinityCategories
