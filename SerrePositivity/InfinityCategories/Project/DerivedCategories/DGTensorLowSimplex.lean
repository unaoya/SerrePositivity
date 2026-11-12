module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTensorTriangleData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedTriangles
/-!
概要：二つの実 dg nerve の0・1・2単体から、対応する tensor 単体を構成する。
方針：閉辺の tensor と、元の三角形の同じ比較 cochain を実単体へ送る。
規約：三つの実二単体面と一単体の面・単位退化を保持する。高次は別工程。
使われ方：dg nerve の直積から tensor nerve への実写像の低次部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
def dgTensorOneSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 1) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) 1 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun i => (s.obj i, t.obj i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorZeroCycle R B C (s.edgeCycle 0 1 (by decide)) (t.edgeCycle 0 1 (by decide)))
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
def dgTensorTwoSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTriangle R B C s.toTriangle t.toTriangle)
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorTwoSimplex_vertex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) (i : Fin 3) :
    (dgTensorTwoSimplex R B C s t).obj i = (s.obj i, t.obj i) := rfl
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorTwoSimplex_homotopy (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    (dgTensorTwoSimplex R B C s t).triangleHom =
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R s.triangleHom
        (_root_.SerrePositivity.DifferentialGraded.compose R (t.edgeHom 1 2 (by decide)) (t.edgeHom 0 1 (by decide))
          (by decide : (0 : ℤ) + 0 = 0)) (by decide : (-1 : ℤ) + 0 = -1) +
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (s.edgeHom 0 2 (by decide)) t.triangleHom
        (by decide : (0 : ℤ) + -1 = -1) := rfl
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorTwoSimplex_face01 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)).δ 2 (dgTensorTwoSimplex R B C s t) =
      dgTensorOneSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).δ 2 s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).δ 2 t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorTwoSimplex_face12 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)).δ 0 (dgTensorTwoSimplex R B C s t) =
      dgTensorOneSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).δ 0 s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).δ 0 t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorTwoSimplex_face02 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)).δ 1 (dgTensorTwoSimplex R B C s t) =
      dgTensorOneSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).δ 1 s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).δ 1 t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
def dgTensorZeroSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 0) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) 0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (s.obj 0, t.obj 0)
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorOneSimplex_face0 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 1) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)).δ 1 (dgTensorOneSimplex R B C s t) =
      dgTensorZeroSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).δ 1 s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).δ 1 t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorOneSimplex_face1 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 1) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)).δ 0 (dgTensorOneSimplex R B C s t) =
      dgTensorZeroSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).δ 0 s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).δ 0 t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl
/-- 同じ二入力の実低次単体と、その面・単位・比較 cochain を照合する。 -/
lemma dgTensorOneSimplex_sigma (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 0) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 0) :
    dgTensorOneSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).σ 0 s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).σ 0 t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)).σ 0 (dgTensorZeroSimplex R B C s t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    simpa only using! (_root_.SerrePositivity.DifferentialGraded.dgTensor_unitElement R B C (s.obj 0, t.obj 0)).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
